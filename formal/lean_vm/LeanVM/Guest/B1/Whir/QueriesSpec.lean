/-
  LeanVM.Guest.B1.Whir.QueriesSpec

  `opening_queries` at its 50 compiled shapes.
-/

module

public import LeanVM.Guest.B1.Whir.Queries

/-!
# The specializations of `opening_queries`

`opening_queries__L{base}_L{I}_L{blocks}_L{depth}_L{cd}` and its loop helper, each body equal to
its template by kernel evaluation (`stmtsEqb_sound`), and the soundness of each at its shape.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Protocol.Verifier

@[expose] public section

set_option maxRecDepth 100000 in
theorem opening_queries_L0_L16_L6_L14_L5_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 14 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L14_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 14 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 0) (I := 16) (blocks := 6) (pd := 9) (cd := 5)
    (name := "opening_queries__L0_L16_L6_L14_L5") (loop := "__loop435")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 590) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 981) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L0_L16_L6_L15_L5_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 15 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L15_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 15 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 0) (I := 16) (blocks := 6) (pd := 10) (cd := 5)
    (name := "opening_queries__L0_L16_L6_L15_L5") (loop := "__loop434")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 587) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 979) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L0_L16_L6_L16_L4_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 16 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L16_L4" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 16 4 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 0) (I := 16) (blocks := 6) (pd := 12) (cd := 4)
    (name := "opening_queries__L0_L16_L6_L16_L4") (loop := "__loop460")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 707) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1012) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L0_L16_L6_L16_L5_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 16 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L16_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 16 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 0) (I := 16) (blocks := 6) (pd := 11) (cd := 5)
    (name := "opening_queries__L0_L16_L6_L16_L5") (loop := "__loop438")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 601) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 985) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L0_L16_L6_L16_L6_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 16 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L16_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 16 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 0) (I := 16) (blocks := 6) (pd := 10) (cd := 6)
    (name := "opening_queries__L0_L16_L6_L16_L6") (loop := "__loop432")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 584) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 976) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L0_L16_L6_L17_L4_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 17 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L17_L4" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 17 4 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 0) (I := 16) (blocks := 6) (pd := 13) (cd := 4)
    (name := "opening_queries__L0_L16_L6_L17_L4") (loop := "__loop462")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 719) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1014) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L0_L16_L6_L17_L5_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 17 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L17_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 17 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 0) (I := 16) (blocks := 6) (pd := 12) (cd := 5)
    (name := "opening_queries__L0_L16_L6_L17_L5") (loop := "__loop441")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 614) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 989) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L0_L16_L6_L17_L6_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 17 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L17_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 17 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 0) (I := 16) (blocks := 6) (pd := 11) (cd := 6)
    (name := "opening_queries__L0_L16_L6_L17_L6") (loop := "__loop437")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 599) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 984) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L0_L16_L6_L18_L4_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 18 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L18_L4" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 18 4 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 0) (I := 16) (blocks := 6) (pd := 14) (cd := 4)
    (name := "opening_queries__L0_L16_L6_L18_L4") (loop := "__loop455")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 675) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1007) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L0_L16_L6_L18_L5_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 18 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L18_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 18 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 0) (I := 16) (blocks := 6) (pd := 13) (cd := 5)
    (name := "opening_queries__L0_L16_L6_L18_L5") (loop := "__loop444")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 629) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 993) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L0_L16_L6_L18_L6_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 18 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L18_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 18 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 0) (I := 16) (blocks := 6) (pd := 12) (cd := 6)
    (name := "opening_queries__L0_L16_L6_L18_L6") (loop := "__loop440")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 612) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 988) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L0_L16_L6_L19_L4_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 19 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L19_L4" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 19 4 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 0) (I := 16) (blocks := 6) (pd := 15) (cd := 4)
    (name := "opening_queries__L0_L16_L6_L19_L4") (loop := "__loop465")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 742) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1017) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L0_L16_L6_L19_L5_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 19 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L19_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 19 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 0) (I := 16) (blocks := 6) (pd := 14) (cd := 5)
    (name := "opening_queries__L0_L16_L6_L19_L5") (loop := "__loop447")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 644) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 997) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L0_L16_L6_L19_L6_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 19 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L19_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 19 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 0) (I := 16) (blocks := 6) (pd := 13) (cd := 6)
    (name := "opening_queries__L0_L16_L6_L19_L6") (loop := "__loop443")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 627) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 992) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L0_L16_L6_L20_L4_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 20 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L20_L4" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 20 4 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 0) (I := 16) (blocks := 6) (pd := 16) (cd := 4)
    (name := "opening_queries__L0_L16_L6_L20_L4") (loop := "__loop469")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 756) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1022) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L0_L16_L6_L20_L5_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 20 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L20_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 20 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 0) (I := 16) (blocks := 6) (pd := 15) (cd := 5)
    (name := "opening_queries__L0_L16_L6_L20_L5") (loop := "__loop450")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 657) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1001) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L0_L16_L6_L20_L6_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 20 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L20_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 20 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 0) (I := 16) (blocks := 6) (pd := 14) (cd := 6)
    (name := "opening_queries__L0_L16_L6_L20_L6") (loop := "__loop446")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 642) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 996) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L0_L16_L6_L21_L4_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 21 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L21_L4" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 21 4 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 0) (I := 16) (blocks := 6) (pd := 17) (cd := 4)
    (name := "opening_queries__L0_L16_L6_L21_L4") (loop := "__loop473")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 828) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1027) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L0_L16_L6_L21_L5_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 21 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L21_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 21 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 0) (I := 16) (blocks := 6) (pd := 16) (cd := 5)
    (name := "opening_queries__L0_L16_L6_L21_L5") (loop := "__loop453")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 670) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1005) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L0_L16_L6_L21_L6_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 21 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L21_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 21 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 0) (I := 16) (blocks := 6) (pd := 15) (cd := 6)
    (name := "opening_queries__L0_L16_L6_L21_L6") (loop := "__loop449")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 655) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1000) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L0_L16_L6_L22_L4_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 22 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L22_L4" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 22 4 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 0) (I := 16) (blocks := 6) (pd := 18) (cd := 4)
    (name := "opening_queries__L0_L16_L6_L22_L4") (loop := "__loop483")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 906) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1038) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L0_L16_L6_L22_L5_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 22 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L22_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 22 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 0) (I := 16) (blocks := 6) (pd := 17) (cd := 5)
    (name := "opening_queries__L0_L16_L6_L22_L5") (loop := "__loop468")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 753) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1021) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L0_L16_L6_L22_L6_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 22 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L22_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 22 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 0) (I := 16) (blocks := 6) (pd := 16) (cd := 6)
    (name := "opening_queries__L0_L16_L6_L22_L6") (loop := "__loop452")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 668) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1004) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L0_L16_L6_L23_L5_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 23 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L23_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 23 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 0) (I := 16) (blocks := 6) (pd := 18) (cd := 5)
    (name := "opening_queries__L0_L16_L6_L23_L5") (loop := "__loop472")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 825) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1026) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L0_L16_L6_L23_L6_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 23 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L23_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 23 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 0) (I := 16) (blocks := 6) (pd := 17) (cd := 6)
    (name := "opening_queries__L0_L16_L6_L23_L6") (loop := "__loop467")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 751) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1020) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L0_L16_L6_L24_L5_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 24 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L24_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 24 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 0) (I := 16) (blocks := 6) (pd := 19) (cd := 5)
    (name := "opening_queries__L0_L16_L6_L24_L5") (loop := "__loop480")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 890) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1034) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L0_L16_L6_L24_L6_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 24 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L24_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 24 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 0) (I := 16) (blocks := 6) (pd := 18) (cd := 6)
    (name := "opening_queries__L0_L16_L6_L24_L6") (loop := "__loop471")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 823) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1025) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L0_L16_L6_L25_L5_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 25 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L0_L16_L6_L25_L5" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 0 16 25 5 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 0) (I := 16) (blocks := 6) (pd := 20) (cd := 5)
    (name := "opening_queries__L0_L16_L6_L25_L5") (loop := "__loop482")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 902) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1037) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L1_L64_L8_L17_L8_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 17 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L17_L8" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 17 8 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 1) (I := 64) (blocks := 8) (pd := 9) (cd := 8)
    (name := "opening_queries__L1_L64_L8_L17_L8") (loop := "__loop430")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 580) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 973) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L1_L64_L8_L18_L7_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 18 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L18_L7" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 18 7 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 1) (I := 64) (blocks := 8) (pd := 11) (cd := 7)
    (name := "opening_queries__L1_L64_L8_L18_L7") (loop := "__loop457")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 684) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1009) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L1_L64_L8_L18_L8_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 18 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L18_L8" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 18 8 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 1) (I := 64) (blocks := 8) (pd := 10) (cd := 8)
    (name := "opening_queries__L1_L64_L8_L18_L8") (loop := "__loop436")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 597) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 983) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L1_L64_L8_L19_L7_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 19 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L19_L7" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 19 7 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 1) (I := 64) (blocks := 8) (pd := 12) (cd := 7)
    (name := "opening_queries__L1_L64_L8_L19_L7") (loop := "__loop458")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 693) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1010) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L1_L64_L8_L19_L8_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 19 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L19_L8" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 19 8 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 1) (I := 64) (blocks := 8) (pd := 11) (cd := 8)
    (name := "opening_queries__L1_L64_L8_L19_L8") (loop := "__loop439")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 610) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 987) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L1_L64_L8_L20_L6_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 20 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L20_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 20 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 1) (I := 64) (blocks := 8) (pd := 14) (cd := 6)
    (name := "opening_queries__L1_L64_L8_L20_L6") (loop := "__loop474")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 837) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1028) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L1_L64_L8_L20_L7_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 20 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L20_L7" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 20 7 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 1) (I := 64) (blocks := 8) (pd := 13) (cd := 7)
    (name := "opening_queries__L1_L64_L8_L20_L7") (loop := "__loop459")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 702) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1011) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L1_L64_L8_L20_L8_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 20 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L20_L8" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 20 8 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 1) (I := 64) (blocks := 8) (pd := 12) (cd := 8)
    (name := "opening_queries__L1_L64_L8_L20_L8") (loop := "__loop442")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 625) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 991) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L1_L64_L8_L21_L6_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 21 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L21_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 21 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 1) (I := 64) (blocks := 8) (pd := 15) (cd := 6)
    (name := "opening_queries__L1_L64_L8_L21_L6") (loop := "__loop475")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 846) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1029) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L1_L64_L8_L21_L7_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 21 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L21_L7" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 21 7 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 1) (I := 64) (blocks := 8) (pd := 14) (cd := 7)
    (name := "opening_queries__L1_L64_L8_L21_L7") (loop := "__loop461")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 714) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1013) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L1_L64_L8_L21_L8_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 21 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L21_L8" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 21 8 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 1) (I := 64) (blocks := 8) (pd := 13) (cd := 8)
    (name := "opening_queries__L1_L64_L8_L21_L8") (loop := "__loop445")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 640) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 995) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L1_L64_L8_L22_L6_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 22 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L22_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 22 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 1) (I := 64) (blocks := 8) (pd := 16) (cd := 6)
    (name := "opening_queries__L1_L64_L8_L22_L6") (loop := "__loop476")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 855) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1030) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L1_L64_L8_L22_L7_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 22 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L22_L7" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 22 7 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 1) (I := 64) (blocks := 8) (pd := 15) (cd := 7)
    (name := "opening_queries__L1_L64_L8_L22_L7") (loop := "__loop463")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 726) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1015) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L1_L64_L8_L22_L8_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 22 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L22_L8" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 22 8 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 1) (I := 64) (blocks := 8) (pd := 14) (cd := 8)
    (name := "opening_queries__L1_L64_L8_L22_L8") (loop := "__loop448")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 653) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 999) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L1_L64_L8_L23_L6_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 23 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L23_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 23 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 1) (I := 64) (blocks := 8) (pd := 17) (cd := 6)
    (name := "opening_queries__L1_L64_L8_L23_L6") (loop := "__loop477")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 866) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1031) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L1_L64_L8_L23_L7_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 23 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L23_L7" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 23 7 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 1) (I := 64) (blocks := 8) (pd := 16) (cd := 7)
    (name := "opening_queries__L1_L64_L8_L23_L7") (loop := "__loop464")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 737) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1016) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L1_L64_L8_L23_L8_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 23 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L23_L8" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 23 8 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 1) (I := 64) (blocks := 8) (pd := 15) (cd := 8)
    (name := "opening_queries__L1_L64_L8_L23_L8") (loop := "__loop451")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 666) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1003) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L1_L64_L8_L24_L6_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 24 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L24_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 24 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 1) (I := 64) (blocks := 8) (pd := 18) (cd := 6)
    (name := "opening_queries__L1_L64_L8_L24_L6") (loop := "__loop478")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 877) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1032) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L1_L64_L8_L24_L7_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 24 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L24_L7" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 24 7 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 1) (I := 64) (blocks := 8) (pd := 17) (cd := 7)
    (name := "opening_queries__L1_L64_L8_L24_L7") (loop := "__loop466")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 749) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1019) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L1_L64_L8_L25_L6_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 25 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L25_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 25 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 1) (I := 64) (blocks := 8) (pd := 19) (cd := 6)
    (name := "opening_queries__L1_L64_L8_L25_L6") (loop := "__loop479")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 888) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1033) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L1_L64_L8_L25_L7_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 25 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L25_L7" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 25 7 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 1) (I := 64) (blocks := 8) (pd := 18) (cd := 7)
    (name := "opening_queries__L1_L64_L8_L25_L7") (loop := "__loop470")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 821) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1024) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

set_option maxRecDepth 100000 in
theorem opening_queries_L1_L64_L8_L26_L6_sound {rd : Reader} {n : ℕ} (hn : n < ordG) {pos : ℕ → ℕ} {cap flags qw qbp rew : E}
    (hpre : QueryBits rd qbp n 26 pos) {rets : List E}
    (h : coreProgram.Rel rd "opening_queries__L1_L64_L8_L26_L6" [cap, flags, qw, qbp, rew, gen ^ n] rets) :
    ∃ qsc, MeaningOpeningQueries 1 64 26 6 n pos rd qsc [cap, flags, qw, qbp, rew, gen ^ n] rets :=
  opening_queries_sound (base := 1) (I := 64) (blocks := 8) (pd := 20) (cd := 6)
    (name := "opening_queries__L1_L64_L8_L26_L6") (loop := "__loop481")
    ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
    (Program.find?_of_indexOf? (j := 900) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1036) (by decide +kernel) rfl) rfl (stmtsEqb_sound (by decide +kernel))
    hn hpre h

end
end LeanVM.Guest.B1
