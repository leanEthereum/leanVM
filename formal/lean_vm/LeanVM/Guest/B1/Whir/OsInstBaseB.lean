/-
  LeanVM.Guest.B1.Whir.OsInstBaseB

  The bounds `open_stacked`'s callees are complete by: group 1's maxima, the pure callees' sizes, a level's callees by bounded trees from their parts.
-/

module

public import LeanVM.Guest.B1.Whir.OsInstBase
public import LeanVM.Guest.B1.Whir.OsFinal3B

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

/-!
# The callees' bounds (TRIAGE #36)

`OsCalleesMax h1`: group 1's bounds (`OsCalleesAtB`) at most constants at the argument shapes
`open_stacked` calls them with. `OsPureSizes fs`: the trees' sizes of `verify_merkle_cap` and the
residual loops (pure, so complete from their relations, bounded by their trees). `osBd`: a bound
by name at a configuration, the largest of group 1's maxima, the queries' trees (their frame, chain
and loop frames), the caps', the query-position loops' (`sqTot`) and the residual loops' bearing
that name. `osLvKidsAtB_mk`: a level's callees by bounded trees from their parts.
-/

variable {fs : String → ℕ} {cert : String → V → ℕ} {κ : ℕ}

/-- **Group 1's callees' bounds, at most constants**, at the argument shapes `open_stacked` calls them
with (`opening_ood_point` at `g^m`, `m ≤ 22`; `grind_check` at `g^17`). -/
structure OsCalleesMax {fs : String → ℕ} {cert : String → V → ℕ} {k : ℕ} (h1 : OsCalleesAtB fs cert k) : Type where
  foldMax : ℕ
  fold : ∀ a, h1.foldB a ≤ foldMax
  canonicalMax : ℕ
  canonical : ∀ a, h1.canonicalB a ≤ canonicalMax
  oodMax : ℕ
  ood : ∀ a m, a.getD 3 0 = gen ^ m → m ≤ 22 → h1.oodB a ≤ oodMax
  grindMax : ℕ
  grind : ∀ a, a.getD 3 0 = gen ^ Whir.queryGrindingBits → h1.grindB a ≤ grindMax
  finalMsg4Max : ℕ
  finalMsg4 : ∀ a, h1.finalMsg4B a ≤ finalMsg4Max
  finalMsg8Max : ℕ
  finalMsg8 : ∀ a, h1.finalMsg8B a ≤ finalMsg8Max
  finalMsg16Max : ℕ
  finalMsg16 : ∀ a, h1.finalMsg16B a ≤ finalMsg16Max
  finalMsg32Max : ℕ
  finalMsg32 : ∀ a, h1.finalMsg32B a ≤ finalMsg32Max
  rowWeights4Max : ℕ
  rowWeights4 : ∀ a, h1.rowWeights4B a ≤ rowWeights4Max
  rowWeights6Max : ℕ
  rowWeights6 : ∀ a, h1.rowWeights6B a ≤ rowWeights6Max
  foldFinal2Max : ℕ
  foldFinal2 : ∀ a, h1.foldFinal2B a ≤ foldFinal2Max
  foldFinal3Max : ℕ
  foldFinal3 : ∀ a, h1.foldFinal3B a ≤ foldFinal3Max
  foldFinal4Max : ℕ
  foldFinal4 : ∀ a, h1.foldFinal4B a ≤ foldFinal4Max
  foldFinal5Max : ℕ
  foldFinal5 : ∀ a, h1.foldFinal5B a ≤ foldFinal5Max

/-- The caps `open_stacked` calls. -/
def osCapNames : List String := ["verify_merkle_cap__L4", "verify_merkle_cap__L5", "verify_merkle_cap__L6", "verify_merkle_cap__L7", "verify_merkle_cap__L8"]

/-- The residual loops `open_stacked` calls, with their trip counts. -/
def osResLoops : List (String × ℕ) :=
  [("__loop106", 224),
    ("__loop107", 56),
    ("__loop108", 32),
    ("__loop109", 23),
    ("__loop114", 224),
    ("__loop115", 56),
    ("__loop116", 32),
    ("__loop117", 23),
    ("__loop123", 224),
    ("__loop124", 56),
    ("__loop125", 32),
    ("__loop126", 23),
    ("__loop127", 17),
    ("__loop133", 224),
    ("__loop134", 56),
    ("__loop135", 32),
    ("__loop136", 23),
    ("__loop137", 17),
    ("__loop143", 224),
    ("__loop144", 56),
    ("__loop145", 32),
    ("__loop146", 23),
    ("__loop147", 18),
    ("__loop153", 225),
    ("__loop154", 56),
    ("__loop155", 32),
    ("__loop156", 23),
    ("__loop157", 18),
    ("__loop164", 225),
    ("__loop165", 56),
    ("__loop166", 32),
    ("__loop167", 23),
    ("__loop168", 18),
    ("__loop169", 14),
    ("__loop174", 112),
    ("__loop175", 45),
    ("__loop176", 28),
    ("__loop177", 21),
    ("__loop182", 112),
    ("__loop183", 45),
    ("__loop184", 28),
    ("__loop185", 21),
    ("__loop191", 112),
    ("__loop192", 45),
    ("__loop193", 28),
    ("__loop194", 21),
    ("__loop195", 16),
    ("__loop201", 112),
    ("__loop202", 45),
    ("__loop203", 28),
    ("__loop204", 21),
    ("__loop205", 16),
    ("__loop211", 112),
    ("__loop212", 45),
    ("__loop213", 28),
    ("__loop214", 21),
    ("__loop215", 16),
    ("__loop221", 112),
    ("__loop222", 45),
    ("__loop223", 28),
    ("__loop224", 21),
    ("__loop225", 16),
    ("__loop232", 112),
    ("__loop233", 45),
    ("__loop234", 28),
    ("__loop235", 21),
    ("__loop236", 16),
    ("__loop237", 13),
    ("__loop242", 75),
    ("__loop243", 38),
    ("__loop244", 25),
    ("__loop245", 19),
    ("__loop250", 75),
    ("__loop251", 38),
    ("__loop252", 25),
    ("__loop253", 19),
    ("__loop259", 75),
    ("__loop260", 38),
    ("__loop261", 25),
    ("__loop262", 19),
    ("__loop263", 15),
    ("__loop269", 75),
    ("__loop270", 38),
    ("__loop271", 25),
    ("__loop272", 19),
    ("__loop273", 15),
    ("__loop279", 75),
    ("__loop280", 38),
    ("__loop281", 25),
    ("__loop282", 19),
    ("__loop283", 15),
    ("__loop289", 75),
    ("__loop290", 38),
    ("__loop291", 25),
    ("__loop292", 19),
    ("__loop293", 15),
    ("__loop300", 75),
    ("__loop301", 38),
    ("__loop302", 25),
    ("__loop303", 19),
    ("__loop304", 15),
    ("__loop305", 13),
    ("__loop310", 56),
    ("__loop311", 32),
    ("__loop312", 23),
    ("__loop313", 18),
    ("__loop318", 56),
    ("__loop319", 32),
    ("__loop320", 23),
    ("__loop321", 18),
    ("__loop327", 56),
    ("__loop328", 32),
    ("__loop329", 23),
    ("__loop330", 18),
    ("__loop331", 14),
    ("__loop337", 56),
    ("__loop338", 32),
    ("__loop339", 23),
    ("__loop340", 18),
    ("__loop341", 14),
    ("__loop347", 56),
    ("__loop348", 32),
    ("__loop349", 23),
    ("__loop350", 18),
    ("__loop351", 14),
    ("__loop357", 56),
    ("__loop358", 32),
    ("__loop359", 23),
    ("__loop360", 18),
    ("__loop361", 15),
    ("__loop368", 56),
    ("__loop369", 32),
    ("__loop370", 23),
    ("__loop371", 18),
    ("__loop372", 15),
    ("__loop373", 12)]

/-- **The trees' sizes of `open_stacked`'s pure callees**: its caps' and its residual loops' at
their trip counts. -/
structure OsPureSizes (fs : String → ℕ) : Type where
  capB : String → ℕ
  cap : ∀ name ∈ osCapNames, TotalLe coreProgram fs name fun _ => capB name
  resB : String → ℕ
  res : ∀ p ∈ osResLoops, ∀ rd (t : Tree) (args rets : List E), t.name = p.1 → args.take 2 = [1, gen ^ p.2] →
    t.Valid coreProgram rd args rets → t.BufsOk coreProgram → t.total fs ≤ resB p.1

/-- The queries' loop helpers. -/
def osOqLoops : List (String × String) :=
  [("opening_queries__L0_L16_L6_L14_L5", "__loop435"),
    ("opening_queries__L0_L16_L6_L15_L5", "__loop434"),
    ("opening_queries__L0_L16_L6_L16_L4", "__loop460"),
    ("opening_queries__L0_L16_L6_L16_L5", "__loop438"),
    ("opening_queries__L0_L16_L6_L16_L6", "__loop432"),
    ("opening_queries__L0_L16_L6_L17_L4", "__loop462"),
    ("opening_queries__L0_L16_L6_L17_L5", "__loop441"),
    ("opening_queries__L0_L16_L6_L17_L6", "__loop437"),
    ("opening_queries__L0_L16_L6_L18_L4", "__loop455"),
    ("opening_queries__L0_L16_L6_L18_L5", "__loop444"),
    ("opening_queries__L0_L16_L6_L18_L6", "__loop440"),
    ("opening_queries__L0_L16_L6_L19_L4", "__loop465"),
    ("opening_queries__L0_L16_L6_L19_L5", "__loop447"),
    ("opening_queries__L0_L16_L6_L19_L6", "__loop443"),
    ("opening_queries__L0_L16_L6_L20_L4", "__loop469"),
    ("opening_queries__L0_L16_L6_L20_L5", "__loop450"),
    ("opening_queries__L0_L16_L6_L20_L6", "__loop446"),
    ("opening_queries__L0_L16_L6_L21_L4", "__loop473"),
    ("opening_queries__L0_L16_L6_L21_L5", "__loop453"),
    ("opening_queries__L0_L16_L6_L21_L6", "__loop449"),
    ("opening_queries__L0_L16_L6_L22_L4", "__loop483"),
    ("opening_queries__L0_L16_L6_L22_L5", "__loop468"),
    ("opening_queries__L0_L16_L6_L22_L6", "__loop452"),
    ("opening_queries__L0_L16_L6_L23_L5", "__loop472"),
    ("opening_queries__L0_L16_L6_L23_L6", "__loop467"),
    ("opening_queries__L0_L16_L6_L24_L5", "__loop480"),
    ("opening_queries__L0_L16_L6_L24_L6", "__loop471"),
    ("opening_queries__L0_L16_L6_L25_L5", "__loop482"),
    ("opening_queries__L1_L64_L8_L17_L8", "__loop430"),
    ("opening_queries__L1_L64_L8_L18_L7", "__loop457"),
    ("opening_queries__L1_L64_L8_L18_L8", "__loop436"),
    ("opening_queries__L1_L64_L8_L19_L7", "__loop458"),
    ("opening_queries__L1_L64_L8_L19_L8", "__loop439"),
    ("opening_queries__L1_L64_L8_L20_L6", "__loop474"),
    ("opening_queries__L1_L64_L8_L20_L7", "__loop459"),
    ("opening_queries__L1_L64_L8_L20_L8", "__loop442"),
    ("opening_queries__L1_L64_L8_L21_L6", "__loop475"),
    ("opening_queries__L1_L64_L8_L21_L7", "__loop461"),
    ("opening_queries__L1_L64_L8_L21_L8", "__loop445"),
    ("opening_queries__L1_L64_L8_L22_L6", "__loop476"),
    ("opening_queries__L1_L64_L8_L22_L7", "__loop463"),
    ("opening_queries__L1_L64_L8_L22_L8", "__loop448"),
    ("opening_queries__L1_L64_L8_L23_L6", "__loop477"),
    ("opening_queries__L1_L64_L8_L23_L7", "__loop464"),
    ("opening_queries__L1_L64_L8_L23_L8", "__loop451"),
    ("opening_queries__L1_L64_L8_L24_L6", "__loop478"),
    ("opening_queries__L1_L64_L8_L24_L7", "__loop466"),
    ("opening_queries__L1_L64_L8_L25_L6", "__loop479"),
    ("opening_queries__L1_L64_L8_L25_L7", "__loop470"),
    ("opening_queries__L1_L64_L8_L26_L6", "__loop481")]

/-- A queries function's loop helper. -/
def osOqLoop (name : String) : String := ((osOqLoops.find? (·.1 = name)).map (·.2)).getD ""

/-- Group 1's maxima by name. -/
def osG1Pairs {k : ℕ} {h1 : OsCalleesAtB fs cert k} (hm : OsCalleesMax h1) : List (String × ℕ) :=
  [("opening_fold", hm.foldMax),
    ("assert_canonical", hm.canonicalMax),
    ("opening_ood_point", hm.oodMax),
    ("grind_check", hm.grindMax),
    ("opening_final_message__L4", hm.finalMsg4Max),
    ("opening_final_message__L8", hm.finalMsg8Max),
    ("opening_final_message__L16", hm.finalMsg16Max),
    ("opening_final_message__L32", hm.finalMsg32Max),
    ("opening_row_weights__L4_L0", hm.rowWeights4Max),
    ("opening_row_weights__L6_L1", hm.rowWeights6Max),
    ("fold_final_msg__L2", hm.foldFinal2Max),
    ("fold_final_msg__L3", hm.foldFinal3Max),
    ("fold_final_msg__L4", hm.foldFinal4Max),
    ("fold_final_msg__L5", hm.foldFinal5Max)]

/-- The largest value bearing a name. -/
def osPairsMax (ps : List (String × ℕ)) (f : String) : ℕ := (ps.map fun p => if f = p.1 then p.2 else 0).foldr max 0

theorem osPairsMax_ge {ps : List (String × ℕ)} {f : String} {v : ℕ} (h : (f, v) ∈ ps) : v ≤ osPairsMax ps f := by
  induction ps with
  | nil => simp at h
  | cons p ps ih =>
    simp only [osPairsMax, List.map_cons, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · exact le_max_of_le_right (ih h)

theorem os_foldr_max_ge {L : List ℕ} {x : ℕ} (h : x ∈ L) : x ≤ L.foldr max 0 := by
  induction L with
  | nil => simp at h
  | cons y L ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_max_of_le_right (ih h)

/-- A level's bound by name: its queries', cap's, query-position loop's and residual loop's. -/
def osLvBd (fs : String → ℕ) (hp : OsPureSizes fs) (lv : OsLvl) (f : String) : ℕ :=
  max (if f = lv.queriesFn then fs f + (lv.queries + 1) + (lv.queries + 1) * fs (osOqLoop f) else 0)
    (max (if f = lv.verifyCap then hp.capB f else 0)
      (max (if f = lv.sqLoop then sqTot fs lv lv.squeezes 0 else 0) (if f = lv.resLoop then hp.resB f else 0)))

/-- **The callees' bound by name** at a configuration. -/
def osBd (fs : String → ℕ) {cert : String → V → ℕ} {k : ℕ} {h1 : OsCalleesAtB fs cert k} (hm : OsCalleesMax h1)
    (hp : OsPureSizes fs) (cfg : OsCfg) (f : String) : ℕ :=
  max (osPairsMax (osG1Pairs hm) f) (((List.range cfg.levels.length).map fun l => osLvBd fs hp (cfg.lv l) f).foldr max 0)

section Bd

variable {k : ℕ} {h1 : OsCalleesAtB fs cert k} (hm : OsCalleesMax h1) (hp : OsPureSizes fs) (cfg : OsCfg)

theorem osBd_g1 {f : String} {v : ℕ} (h : (f, v) ∈ osG1Pairs hm) : v ≤ osBd fs hm hp cfg f :=
  le_max_of_le_left (osPairsMax_ge h)

theorem osBd_lv {l : ℕ} (hl : l < cfg.levels.length) (f : String) : osLvBd fs hp (cfg.lv l) f ≤ osBd fs hm hp cfg f :=
  le_max_of_le_right (os_foldr_max_ge (List.mem_map.mpr ⟨l, List.mem_range.mpr hl, rfl⟩))

theorem osKB_fold : CompleteRelB fs cert k "opening_fold" MeaningOpeningFold (osBd fs hm hp cfg "opening_fold") :=
  fun a r L h => (h1.fold a r L h).mono le_rfl ((hm.fold a).trans (osBd_g1 hm hp cfg (by simp [osG1Pairs])))

theorem osKB_canonical : CompleteRelB fs cert k "assert_canonical" (fun _ args rets => MeaningAssertCanonical args rets)
    (osBd fs hm hp cfg "assert_canonical") :=
  fun a r L h => (h1.canonical a r L h).mono le_rfl ((hm.canonical a).trans (osBd_g1 hm hp cfg (by simp [osG1Pairs])))

theorem osKB_ood : OsOodAtB fs cert k (osBd fs hm hp cfg "opening_ood_point") :=
  fun m h22 a r L ha h => (h1.ood a r L h).mono le_rfl
    ((hm.ood a m ha h22).trans (osBd_g1 hm hp cfg (by simp [osG1Pairs])))

theorem osKB_grind : OsGrindAtB fs cert k (osBd fs hm hp cfg "grind_check") :=
  fun a r L ha h => (h1.grind a r L h).mono le_rfl ((hm.grind a ha).trans (osBd_g1 hm hp cfg (by simp [osG1Pairs])))

theorem osKB_finalMsg4 : OsFinalMsgAtB fs cert k "opening_final_message__L4" 4 fun _ => osBd fs hm hp cfg "opening_final_message__L4" :=
  fun a r L h => (h1.finalMsg4 a r L h).mono le_rfl ((hm.finalMsg4 a).trans (osBd_g1 hm hp cfg (by simp [osG1Pairs])))

theorem osKB_finalMsg8 : OsFinalMsgAtB fs cert k "opening_final_message__L8" 8 fun _ => osBd fs hm hp cfg "opening_final_message__L8" :=
  fun a r L h => (h1.finalMsg8 a r L h).mono le_rfl ((hm.finalMsg8 a).trans (osBd_g1 hm hp cfg (by simp [osG1Pairs])))

theorem osKB_finalMsg16 : OsFinalMsgAtB fs cert k "opening_final_message__L16" 16 fun _ => osBd fs hm hp cfg "opening_final_message__L16" :=
  fun a r L h => (h1.finalMsg16 a r L h).mono le_rfl ((hm.finalMsg16 a).trans (osBd_g1 hm hp cfg (by simp [osG1Pairs])))

theorem osKB_finalMsg32 : OsFinalMsgAtB fs cert k "opening_final_message__L32" 32 fun _ => osBd fs hm hp cfg "opening_final_message__L32" :=
  fun a r L h => (h1.finalMsg32 a r L h).mono le_rfl ((hm.finalMsg32 a).trans (osBd_g1 hm hp cfg (by simp [osG1Pairs])))

theorem osKB_rowWeights4 : OsRowWeightsAtB fs cert k "opening_row_weights__L4_L0" 4 0 fun _ => osBd fs hm hp cfg "opening_row_weights__L4_L0" :=
  fun a r L h => (h1.rowWeights4 a r L h).mono le_rfl ((hm.rowWeights4 a).trans (osBd_g1 hm hp cfg (by simp [osG1Pairs])))

theorem osKB_rowWeights6 : OsRowWeightsAtB fs cert k "opening_row_weights__L6_L1" 6 1 fun _ => osBd fs hm hp cfg "opening_row_weights__L6_L1" :=
  fun a r L h => (h1.rowWeights6 a r L h).mono le_rfl ((hm.rowWeights6 a).trans (osBd_g1 hm hp cfg (by simp [osG1Pairs])))

theorem osKB_foldFinal2 : OsFoldFinalAtB fs cert k "fold_final_msg__L2" 2 fun _ => osBd fs hm hp cfg "fold_final_msg__L2" :=
  fun a r L h => (h1.foldFinal2 a r L h).mono le_rfl ((hm.foldFinal2 a).trans (osBd_g1 hm hp cfg (by simp [osG1Pairs])))

theorem osKB_foldFinal3 : OsFoldFinalAtB fs cert k "fold_final_msg__L3" 3 fun _ => osBd fs hm hp cfg "fold_final_msg__L3" :=
  fun a r L h => (h1.foldFinal3 a r L h).mono le_rfl ((hm.foldFinal3 a).trans (osBd_g1 hm hp cfg (by simp [osG1Pairs])))

theorem osKB_foldFinal4 : OsFoldFinalAtB fs cert k "fold_final_msg__L4" 4 fun _ => osBd fs hm hp cfg "fold_final_msg__L4" :=
  fun a r L h => (h1.foldFinal4 a r L h).mono le_rfl ((hm.foldFinal4 a).trans (osBd_g1 hm hp cfg (by simp [osG1Pairs])))

theorem osKB_foldFinal5 : OsFoldFinalAtB fs cert k "fold_final_msg__L5" 5 fun _ => osBd fs hm hp cfg "fold_final_msg__L5" :=
  fun a r L h => (h1.foldFinal5 a r L h).mono le_rfl ((hm.foldFinal5 a).trans (osBd_g1 hm hp cfg (by simp [osG1Pairs])))

end Bd

theorem VmcCompleteAtB.mono {k D : ℕ} {name : String} {B B' : ℕ} (h : VmcCompleteAtB fs cert k D name B) (hB : B ≤ B') :
    VmcCompleteAtB fs cert k D name B' := fun L c f r hm => (h L c f r hm).mono le_rfl hB

/-- **A level's callees by bounded trees, from their parts.** -/
theorem osLvKidsAtB_mk {k : ℕ} {h1 : OsCalleesAtB fs cert k} {hm : OsCalleesMax h1} {hp : OsPureSizes fs} {cfg : OsCfg}
    {l : ℕ} (hl : l < cfg.levels.length)
    (hrw : OsRowWeightsAtB fs cert κ (cfg.lv l).rowWeights (cfg.lv l).folds (if l = 0 then 1 else 0)
      fun _ => osBd fs hm hp cfg (cfg.lv l).rowWeights)
    (hcn : (cfg.lv l).verifyCap ∈ osCapNames)
    (hcap : ∀ {B : ℕ}, TotalLe coreProgram fs (cfg.lv l).verifyCap (fun _ => B) →
      VmcCompleteAtB fs cert κ (cfg.lv l).capDepth (cfg.lv l).verifyCap B) {loop : String}
    (hq : OqCompleteAtB fs cert κ (if l = 0 then 1 else 0) (2 ^ (cfg.lv l).folds) (cfg.lv l).depth
      (cfg.lv l).capDepth (cfg.lv l).queriesFn fun n => fs (cfg.lv l).queriesFn + (n + 1) + (n + 1) * fs loop)
    (hloop : osOqLoop (cfg.lv l).queriesFn = loop)
    (hdec : OsDecodeAtD fs cert κ (cfg.lv l).depth (cfg.lv l).decode) (hpl : sqPlaceB (cfg.lv l) = true)
    {fn : Fn} (hsf : coreProgram.find? (cfg.lv l).sqLoop = some fn) (hsp : fn.params = [.n 0, .n 1, .n 2, .n 3, .n 4])
    (hsb : fn.body = sqLoopOf (cfg.lv l)) (hsl : coreProgram.loop (cfg.lv l).sqLoop = true) {fr : Fn}
    (hrf : coreProgram.find? (cfg.lv l).resLoop = some fr)
    (hrp : fr.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6]) (hrb : fr.body = resLoopOf cfg l (cfg.lv l))
    (hpure : Stmt.pureList [(cfg.lv l).resLoop] (resLoopOf cfg l (cfg.lv l)) = true)
    (hres : ((cfg.lv l).resLoop, (cfg.lv l).queries) ∈ osResLoops) :
    OsLvKidsAtB fs cert κ cfg (osBd fs hm hp cfg) l where
  rw := hrw
  cap := (hcap (hp.cap _ hcn)).mono <| le_trans (le_max_of_le_right (le_max_of_le_left (by simp)))
    (osBd_lv hm hp cfg hl _)
  queries := ⟨_, hq, le_trans (by rw [← hloop]; exact le_max_of_le_left (by simp)) (osBd_lv hm hp cfg hl _)⟩
  decode := hdec
  sqPlace := sqPlace_of hpl
  sqFn := ⟨fn, hsf, hsp, hsb⟩
  sqLoop := hsl
  sqLe := le_trans (le_max_of_le_right (le_max_of_le_right (le_max_of_le_left (by simp))))
    (osBd_lv hm hp cfg hl _)
  resPure := fun g hg f hf => by
    simp only [List.mem_singleton] at hg
    subst hg
    rw [hrf] at hf
    cases hf
    rw [hrb]
    exact hpure
  resFn := ⟨fr, hrf, hrp, hrb⟩
  resTot := fun rd t args rets hn ha hv hb => le_trans (hp.res _ hres rd t args rets hn ha hv hb)
    (le_trans (le_max_of_le_right (le_max_of_le_right (le_max_of_le_right (by simp)))) (osBd_lv hm hp cfg hl _))

end
end LeanVM.Guest.B1
