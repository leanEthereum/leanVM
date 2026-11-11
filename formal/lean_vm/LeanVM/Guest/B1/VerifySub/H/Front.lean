/-
  LeanVM.Guest.B1.VerifySub.H.Front

  `verify_sub`'s honest valuation against an honest child's run: the announced words, the root,
  the bus challenges and `β` are the run's.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Sponge
public import LeanVM.Guest.B1.VerifySub.Segments
public import LeanVM.Guest.B1.VerifySub.FrontAll
public import LeanVM.Guest.B1.Placement.Kappas
public import LeanVM.Guest.B1.Tables.VtC.AHon

/-!
# The front against the child's run

`vsH_heights`: an honest child's table heights are below `29` (each is a committed column's log,
at most the stack's log `≤ 28`). `vsH_spec`: on the statement's and the seed's cells, with the
child's stream's first ten words in memory at `stream`, the honest valuation reads the announced
words and the root of the run (`ChildSegs`), and its bus challenges, its capacity after them and
`β` are the run's.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier LeanVM.Node

@[expose] public section

/-- **An honest layout's table heights are at most its stack's log `B`.** -/
theorem vsH_heights {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {logMem : ℕ}
    {rowsN : List ℕ} (hrl : rowsN.length = 6) {B : ℕ}
    (h28 : (Tables.layoutOf bytecode logMem rowsN).stackLog ≤ B) :
    ∀ h ∈ Tables.tableHeightsOf rowsN, h < B + 1 := by
  have hsl := tableHeights_length rowsN hrl
  rw [stackLog_eq hbl] at h28
  have hk : ∀ c < Tables.nCommittedCols, (Tables.committedKappas
      (columnKappas logMem Tables.guestLogBytecode (Tables.tableHeightsOf rowsN))).getD c 0 ≤ B := by
    intro c hc
    have hcl : c < (Tables.committedKappas (columnKappas logMem Tables.guestLogBytecode
        (Tables.tableHeightsOf rowsN))).length := by
      rw [Tables.committedKappas_length _ (Tables.columnKappas_length _ _ _)]; exact hc
    have := Tables.tb_le_log2Ceil_of_two_pow_le (Tables.tb_single_le_sum_map _ c hcl)
    have e : ((Tables.committedKappas (columnKappas logMem Tables.guestLogBytecode
        (Tables.tableHeightsOf rowsN))).map (2 ^ ·)).sum =
        Tables.stackTotal (columnKappas logMem 19 (Tables.tableHeightsOf rowsN)) := rfl
    rw [e] at this
    omega
  rw [Tables.committedKappas_columnKappas logMem _ hsl] at hk
  intro h hh
  obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hh
  rw [hsl] at ht
  have key : ∀ c < Tables.nCommittedCols, (0 :: logMem :: Tables.tableHeightsOf rowsN).getD
      (Tables.colKappaSrc c) 0 + Tables.colKappaAdj c ≤ B := fun c hc ↦ by
    have := hk c hc
    rwa [List.getD_eq_getElem _ _ (by simpa using hc), List.getElem_map, List.getElem_range] at this
  have e : (Tables.tableHeightsOf rowsN)[t] = (Tables.tableHeightsOf rowsN).getD t 0 :=
    (List.getD_eq_getElem _ _ _).symm
  rw [e]
  interval_cases t
  · have := key 6 (by decide); simp [Tables.colKappaSrc, Tables.colKappaAdj] at this; rw [List.getD_eq_getElem?_getD]; omega
  · have := key 21 (by decide); simp [Tables.colKappaSrc, Tables.colKappaAdj] at this; rw [List.getD_eq_getElem?_getD]; omega
  · have := key 36 (by decide); simp [Tables.colKappaSrc, Tables.colKappaAdj] at this; rw [List.getD_eq_getElem?_getD]; omega
  · have := key 44 (by decide); simp [Tables.colKappaSrc, Tables.colKappaAdj] at this; rw [List.getD_eq_getElem?_getD]; omega
  · have := key 59 (by decide); simp [Tables.colKappaSrc, Tables.colKappaAdj] at this; rw [List.getD_eq_getElem?_getD]; omega
  · have := key 73 (by decide); simp [Tables.colKappaSrc, Tables.colKappaAdj] at this; rw [List.getD_eq_getElem?_getD]; omega

/-- **An honest `KECCAK` height is at most `26`.** -/
theorem vsH_tau26 {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {logMem : ℕ}
    {rowsN : List ℕ} (hrl : rowsN.length = 6)
    (h28 : (Tables.layoutOf bytecode logMem rowsN).stackLog ≤ 32) :
    (Tables.tableHeightsOf rowsN).getD 5 0 ≤ 26 := by
  have hsl := tableHeights_length rowsN hrl
  rw [stackLog_eq hbl] at h28
  have hcl : 5 < (Tables.committedKappas (columnKappas logMem Tables.guestLogBytecode
      (Tables.tableHeightsOf rowsN))).length := by
    rw [Tables.committedKappas_length _ (Tables.columnKappas_length _ _ _)]; show 5 < 101; norm_num
  have := Tables.tb_le_log2Ceil_of_two_pow_le (Tables.tb_single_le_sum_map _ 5 hcl)
  have e : ((Tables.committedKappas (columnKappas logMem Tables.guestLogBytecode
      (Tables.tableHeightsOf rowsN))).map (2 ^ ·)).sum =
      Tables.stackTotal (columnKappas logMem 19 (Tables.tableHeightsOf rowsN)) := rfl
  rw [e, Tables.committedKappas_columnKappas logMem _ hsl,
    List.getD_eq_getElem _ _ (by simp; show 5 < 101; norm_num), List.getElem_map, List.getElem_range] at this
  simp [Tables.colKappaSrc, Tables.colKappaAdj] at this
  rw [List.getD_eq_getElem?_getD]
  omega

/-- The announced words of an honest child. -/
def ChildSegs.words {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c) :
    List E :=
  eOfNat S.logMem :: S.rowsN.map eOfNat ++ [eOfNat S.rate]

theorem ChildSegs.words_length {bytecode : List K} {seed : Digest} {c : Child}
    (S : ChildSegs bytecode seed c) : S.words.length = 8 := by
  simp [ChildSegs.words, S.hrowsL]

theorem ChildSegs.stream_getD {bytecode : List K} {seed : Digest} {c : Child}
    (S : ChildSegs bytecode seed c) :
    (∀ i < 8, c.proof.stream.getD i 0 = S.words.getD i 0) ∧ c.proof.stream.getD 8 0 = S.x0 ∧
      c.proof.stream.getD 9 0 = S.x1 := by
  have e : c.proof.stream = S.words ++ (S.x0 :: S.x1 :: (S.xsG ++ S.xsT ++ S.xsK ++ S.xsW)) := by
    rw [S.hstream, ChildSegs.words]; simp
  have hl := S.words_length
  refine ⟨fun i hi ↦ ?_, ?_, ?_⟩
  · rw [e, List.getD_append _ _ _ _ (by omega)]
  · rw [e, List.getD_append_right _ _ _ _ (by omega), hl]; rfl
  · rw [e, List.getD_append_right _ _ _ _ (by omega), hl]; rfl

theorem digest_inj {d d' : Digest} (h : digestHalves d = digestHalves d') : d = d' := by
  have e := digestOfScalars_digestScalars d
  rw [h, digestOfScalars_digestScalars d'] at e
  exact (Option.some.inj e).symm

theorem digest_canonical (d : Digest) :
    IsCanonical128 (digestHalves d).1 ∧ IsCanonical128 (digestHalves d).2 := by
  have h := digestOfScalars_digestScalars d
  unfold digestFromHalves at h
  split at h
  · rename_i hc; exact hc
  · simp at h

/-- The seed's state carries a sponge. -/
theorem seed_carries (seed pi : Digest) :
    ∃ sp, (⟨capOf (keccakF1600 (seedInput seed pi)), []⟩ : Fs).Carries sp :=
  ⟨⟨keccakF1600 (seedInput seed pi), []⟩, rfl, rfl⟩

/-- **What the honest front is, against the run.** -/
structure VsFrontH {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)
    (rd : Reader) (σ : Val) : Prop extends VsFrontS rd σ c.proof.stream where
  hcap0 : [σ (.n 20), σ (.n 21), σ (.n 22), σ (.n 23), σ (.n 24)] =
    capOf (keccakF1600 (seedInput seed (statementDigest seed c.statement)))
  hwords : vsWords σ = S.words
  h537 : σ (.n 324) = S.x0
  h547 : σ (.n 334) = S.x1
  hs1 : S.s1 = ⟨[σ (.n 75), σ (.n 76), σ (.n 77), σ (.n 78), σ (.n 79)],
      [(σ (.n 80), dsObserve), (σ (.n 90), dsObserve), (σ (.n 100), dsObserve),
        (σ (.n 110), dsObserve)]⟩
  halphas : vsAlphas σ = S.alphas
  hs3 : S.s3 = ⟨[σ (.n 415), σ (.n 416), σ (.n 417), σ (.n 418), σ (.n 419)], []⟩
  hβ : σ (.n 623) = S.s3.squeeze.1
  hs4 : S.s3.squeeze.2 = ⟨[σ (.n 612), σ (.n 613), σ (.n 614), σ (.n 615), σ (.n 616)], []⟩

variable {rd : Reader} {w : ℕ → E} {args : List E}

/-- **The honest front is the run's.** -/
theorem vsH_spec {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {seed : Digest} {c : Child}
    (S : ChildSegs bytecode seed c) {sq out : E}
    (hargs : args = [(digestHalves (statementDigest seed c.statement)).1,
      (digestHalves (statementDigest seed c.statement)).2, (digestHalves seed).1,
      (digestHalves seed).2, sq, out])
    (hws : ∀ i < 10, LoadHolds rd (vsσ rd w args (.n 25)) i (c.proof.stream.getD i 0)) :
    VsFrontH S rd (vsσ rd w args) := by
  have hl : args.length = 6 := by rw [hargs]; rfl
  have hc4 : ∀ i < 4, IsCanonical128 (args.getD i 0) := by
    intro i hi
    have c1 := digest_canonical (statementDigest seed c.statement)
    have c2 := digest_canonical seed
    rw [hargs]
    interval_cases i
    · exact c1.1
    · exact c1.2
    · exact c2.1
    · exact c2.2
  have F := vsH_front (rd := rd) (w := w) hl hc4 hws
  generalize hσ : vsσ rd w args = σ at F hws ⊢
  have hp : ∀ i < 6, σ (.n i) = args.getD i 0 := fun i hi ↦ by rw [← hσ]; exact vsC_param hl hi
  obtain ⟨hw8, hx8, hx9⟩ := S.stream_getD
  -- the seed
  obtain ⟨seed', pi', es, ep, hcap0⟩ := vs_seed F.hseed (F.hz 8 (by simp)) (F.hz 9 (by simp))
    (F.hz 10 (by simp)) (F.hz 11 (by simp))
  have es' : seed' = seed := by
    apply digest_inj
    rw [← es, hp 2 (by norm_num), hp 3 (by norm_num), hargs]; rfl
  have ep' : pi' = statementDigest seed c.statement := by
    apply digest_inj
    rw [← ep, hp 0 (by norm_num), hp 1 (by norm_num), hargs]; rfl
  rw [es', ep'] at hcap0
  -- the announced words
  have hwords : vsWords σ = S.words := by
    apply List.ext_getElem (by rw [S.words_length]; rfl)
    intro i h1 h2
    have hi : i < 8 := by simpa [vsWords] using h1
    have e := F.hx i hi
    rw [hw8 i hi, List.getD_eq_getElem _ _ h2] at e
    rw [← e]
    interval_cases i <;> rfl
  have e537 : σ (.n 324) = S.x0 := by rw [F.e537, hx8]
  have e547 : σ (.n 334) = S.x1 := by rw [F.e547, hx9]
  -- the announced sizes' run
  have hh := vsH_heights (B := 30) hbl S.hrowsL (by rw [← S.hlayout]; exact S.hmu30)
  have hr := readSizes_runsTo hbl S.hlm1 S.h30 S.hrowsL hh S.hr1 S.hr4 (by rw [← S.hlayout]; exact S.hmu30)
    (⟨capOf (keccakF1600 (seedInput seed (statementDigest seed c.statement))), []⟩ : Fs)
  rw [← S.hlayout] at hr
  obtain ⟨-, es1, -⟩ := Tables.runsTo_det S.runS hr (seed_carries _ _) (r1 := []) (r2 := []) rfl
  have hs1 : S.s1 = ⟨[σ (.n 75), σ (.n 76), σ (.n 77), σ (.n 78), σ (.n 79)],
      [(σ (.n 80), dsObserve), (σ (.n 90), dsObserve), (σ (.n 100), dsObserve),
        (σ (.n 110), dsObserve)]⟩ := by
    rw [es1, ← hcap0, ← F.hab8, hwords, ChildSegs.words]
  -- the bus challenges and `β`
  have hab : (S.s1.absorb S.x0 dsObserve).absorb S.x1 dsObserve =
      ⟨[σ (.n 319), σ (.n 320), σ (.n 321), σ (.n 322), σ (.n 323)],
        [(σ (.n 324), dsObserve), (σ (.n 334), dsObserve)]⟩ := by
    rw [hs1, ← e537, ← e547]; exact F.habR
  have ha := S.halphas
  rw [hab, show busBits = 4 from rfl, F.halpha] at ha
  simp only [Prod.mk.injEq] at ha
  obtain ⟨ea, es3⟩ := ha
  refine ⟨F, hcap0, hwords, e537, e547, hs1, ea, es3.symm, ?_, ?_⟩
  · rw [← es3, F.hbeta]
  · rw [← es3, F.hbeta]

end
end LeanVM.Guest.B1.VerifySub
