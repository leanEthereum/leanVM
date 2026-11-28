/-
  LeanVM.Guest.B1.VsC.VsNatSec

  The link section's runs are sound at the honest context: every definition they make is a
  defining equation of `verify_sub`'s forward valuation, or `θ_0`'s store into `.n 10`.
-/

module

public import LeanVM.Guest.B1.VsC.VsNatHid
public import LeanVM.Guest.B1.Link.Arith.SectionRun
public import LeanVM.Guest.B1.Link.Arith.ExecGood

/-!
# The link section at the honest context

`linkSecStatement` asks every atom of `linkSec` to hold at `(rd0, σ0)`, which needs each load's pointer in
`K`, each store's word, each divisor nonzero and each assertion. Its proof uses the atoms only through the two
symbolic runs (`runP`, `runR`) and the stores at `shifts`, so `linkSecStatementRun` asks only the runs'
soundness (`LinkSecRuns`). Here:

* **`linkSec_eq`**: `linkSec` is `vsC`'s statements `59 ..< 59 + 2419`, so its atoms satisfy `Good` on
  `verify_sub`'s forward valuation (`vsVal_goodC`);
* **`vsStores_ok`**, **`chkRun_runP`**, **`chkRun_runR`** (the kernel): `vsC`'s stores are among `vsStoresT`,
  and every definition each run makes is a constant, a sum, a copy, a product of older values or a load not
  among the stores, but `θ_0`'s store `.load (.n 573) (.n 10) 0` (statement `571`: `.n 573` is
  `opening_message`'s return, which the run defines from the word it stores);
* **`linkSecRuns_of_good`**: `LinkSecRuns` on every forward valuation whose `θ_0` store holds;
* **`VsCtx.linkSecAtoms_honest`**: `LinkSecRuns x.rd0 x.σ0` from `x.Ok`, the buffers' sizes, a causal return
  rule and `Bw1.b4` (buffer `4`'s word `0` is `w 573`);
* **`VsCtx.linkSecVals_of_runs`**: `LinkSecVals` from `LinkSecRuns`, the section's reads (`IRReads`) and the
  overlay's fresh loads (`VsFresh`), the shift coefficients the overlay's words.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Link LeanVM.Node LeanVM.Protocol
open LeanVM.Protocol.Verifier LeanVM.Protocol.Compile LeanVM.Protocol.Link
open LeanVM.Guest.B1.Link.Arith (tailRowSide tailLets tailIn LinkSecRuns TrieSound runP runR chkRun stTriple
  exec_evalG linkSec)

@[expose] public section

/-! ## The section within `vsC` -/

theorem linkSec_eq : linkSec = (vsC.drop 59).take 2419 := by
  rw [vsC, List.drop_take, List.drop_drop, List.take_take]
  rfl

theorem linkSec_good {rd : Reader} {w : ℕ → E} {args : List E} (ha : args.length = 6) :
    ∀ a, Stmt.atom a ∈ linkSec → Good rd (storesOf 482 vsC) w (vsVal rd w args) a := fun a h =>
  vsVal_goodC (rd := rd) (w := w) ha (.atom a) (by
    rw [linkSec_eq] at h
    exact List.mem_of_mem_drop (List.mem_of_mem_take h))

/-! ## The kernel's checks -/

/-- `vsC`'s stores: value, pointer, offset. -/
def vsStoresT : List (ℕ × ℕ × ℕ) := [
    (573, 10, 0), (698, 11, 0), (696, 11, 1), (703, 11, 2), (704, 11, 4), (706, 11, 3), (707, 11, 5),
    (712, 11, 6), (713, 11, 10), (715, 11, 7), (716, 11, 11), (718, 11, 8), (719, 11, 12), (721, 11, 9),
    (722, 11, 13), (727, 11, 14), (728, 11, 22), (730, 11, 15), (731, 11, 23), (733, 11, 16), (734, 11, 24),
    (736, 11, 17), (737, 11, 25), (739, 11, 18), (740, 11, 26), (742, 11, 19), (743, 11, 27), (745, 11, 20),
    (746, 11, 28), (748, 11, 21), (749, 11, 29), (1080, 17, 0), (1078, 17, 1), (1085, 17, 2), (1086, 17, 4),
    (1088, 17, 3), (1089, 17, 5), (1094, 17, 6), (1095, 17, 10), (1097, 17, 7), (1098, 17, 11), (1100, 17, 8),
    (1101, 17, 12), (1103, 17, 9), (1104, 17, 13), (1109, 17, 14), (1110, 17, 22), (1112, 17, 15),
    (1113, 17, 23), (1115, 17, 16), (1116, 17, 24), (1118, 17, 17), (1119, 17, 25), (1121, 17, 18),
    (1122, 17, 26), (1124, 17, 19), (1125, 17, 27), (1127, 17, 20), (1128, 17, 28), (1130, 17, 21),
    (1131, 17, 29), (1136, 17, 30), (1137, 17, 46), (1139, 17, 31), (1140, 17, 47), (1142, 17, 32),
    (1143, 17, 48), (1145, 17, 33), (1146, 17, 49), (1148, 17, 34), (1149, 17, 50), (1151, 17, 35),
    (1152, 17, 51), (1154, 17, 36), (1155, 17, 52), (1157, 17, 37), (1158, 17, 53), (1160, 17, 38),
    (1161, 17, 54), (1163, 17, 39), (1164, 17, 55), (1166, 17, 40), (1167, 17, 56), (1169, 17, 41),
    (1170, 17, 57), (1172, 17, 42), (1173, 17, 58), (1175, 17, 43), (1176, 17, 59), (1178, 17, 44),
    (1179, 17, 60), (1181, 17, 45), (1182, 17, 61), (1187, 17, 62), (1188, 17, 94), (1190, 17, 63),
    (1191, 17, 95), (1193, 17, 64), (1194, 17, 96), (1196, 17, 65), (1197, 17, 97), (1199, 17, 66),
    (1200, 17, 98), (1202, 17, 67), (1203, 17, 99), (1205, 17, 68), (1206, 17, 100), (1208, 17, 69),
    (1209, 17, 101), (1211, 17, 70), (1212, 17, 102), (1214, 17, 71), (1215, 17, 103), (1217, 17, 72),
    (1218, 17, 104), (1220, 17, 73), (1221, 17, 105), (1223, 17, 74), (1224, 17, 106), (1226, 17, 75),
    (1227, 17, 107), (1229, 17, 76), (1230, 17, 108), (1232, 17, 77), (1233, 17, 109), (1235, 17, 78),
    (1236, 17, 110), (1238, 17, 79), (1239, 17, 111), (1241, 17, 80), (1242, 17, 112), (1244, 17, 81),
    (1245, 17, 113), (1247, 17, 82), (1248, 17, 114), (1250, 17, 83), (1251, 17, 115), (1253, 17, 84),
    (1254, 17, 116), (1256, 17, 85), (1257, 17, 117), (1259, 17, 86), (1260, 17, 118), (1262, 17, 87),
    (1263, 17, 119), (1265, 17, 88), (1266, 17, 120), (1268, 17, 89), (1269, 17, 121), (1271, 17, 90),
    (1272, 17, 122), (1274, 17, 91), (1275, 17, 123), (1277, 17, 92), (1278, 17, 124), (1280, 17, 93),
    (1281, 17, 125), (2854, 19, 0), (2862, 19, 1), (2870, 19, 2), (2872, 19, 3), (2874, 19, 4), (2876, 19, 5),
    (2878, 19, 6), (2880, 19, 7), (2882, 19, 8), (2884, 19, 9), (2886, 19, 10), (2888, 19, 11), (2997, 3039, 0),
    (2998, 3039, 1), (2999, 3039, 2), (3000, 3039, 3), (3001, 3039, 4), (3002, 3039, 5), (3003, 3039, 6),
    (3017, 3039, 7), (3018, 3039, 8), (3019, 3039, 9), (3020, 3039, 10), (3021, 3039, 11), (3022, 3039, 12),
    (3023, 3039, 13), (3024, 3039, 14), (3038, 3039, 15), (3041, 3040, 0), (3050, 3040, 8), (3059, 3040, 16),
    (3068, 3040, 24), (3077, 3040, 32), (3086, 3040, 40), (3095, 3040, 48), (3104, 3040, 56), (3105, 3040, 1),
    (3114, 3040, 9), (3123, 3040, 17), (3132, 3040, 25), (3141, 3040, 33), (3150, 3040, 41), (3159, 3040, 49),
    (3168, 3040, 57), (3169, 3040, 2), (3178, 3040, 10), (3187, 3040, 18), (3196, 3040, 26), (3205, 3040, 34),
    (3214, 3040, 42), (3223, 3040, 50), (3232, 3040, 58), (3233, 3040, 3), (3242, 3040, 11), (3251, 3040, 19),
    (3260, 3040, 27), (3269, 3040, 35), (3278, 3040, 43), (3287, 3040, 51), (3296, 3040, 59), (3297, 3040, 4),
    (3306, 3040, 12), (3315, 3040, 20), (3324, 3040, 28), (3333, 3040, 36), (3342, 3040, 44), (3351, 3040, 52),
    (3360, 3040, 60), (3361, 3040, 5), (3370, 3040, 13), (3379, 3040, 21), (3388, 3040, 29), (3397, 3040, 37),
    (3406, 3040, 45), (3415, 3040, 53), (3424, 3040, 61), (3425, 3040, 6), (3434, 3040, 14), (3443, 3040, 22),
    (3452, 3040, 30), (3461, 3040, 38), (3470, 3040, 46), (3479, 3040, 54), (3488, 3040, 62), (3489, 3040, 7),
    (3498, 3040, 15), (3507, 3040, 23), (3516, 3040, 31), (3525, 3040, 39), (3534, 3040, 47), (3543, 3040, 55),
    (3552, 3040, 63), (3557, 3553, 0), (3561, 3553, 1), (3565, 3553, 2), (3569, 3553, 3), (3573, 3553, 4),
    (3577, 3553, 5), (3581, 3553, 6), (3585, 3553, 7), (3589, 3553, 8), (3593, 3553, 9), (3597, 3553, 10),
    (3601, 3553, 11), (3605, 3553, 12), (3609, 3553, 13), (3613, 3553, 14), (3617, 3553, 15), (3621, 3553, 16),
    (3625, 3553, 17), (3629, 3553, 18), (3633, 3553, 19), (3637, 3553, 20), (3641, 3553, 21), (3645, 3553, 22),
    (3649, 3553, 23), (3653, 3553, 24), (3657, 3553, 25), (3661, 3553, 26), (3665, 3553, 27), (3669, 3553, 28),
    (3673, 3553, 29), (3677, 3553, 30), (3681, 3553, 31), (3685, 3553, 32), (3689, 3553, 33), (3693, 3553, 34),
    (3697, 3553, 35), (3701, 3553, 36), (3705, 3553, 37), (3709, 3553, 38), (3713, 3553, 39), (3717, 3553, 40),
    (3721, 3553, 41), (3725, 3553, 42), (3729, 3553, 43), (3733, 3553, 44), (3737, 3553, 45), (3741, 3553, 46),
    (3745, 3553, 47), (3749, 3553, 48), (3753, 3553, 49), (3757, 3553, 50), (3761, 3553, 51), (3765, 3553, 52),
    (3769, 3553, 53), (3773, 3553, 54), (3777, 3553, 55), (3781, 3553, 56), (3785, 3553, 57), (3789, 3553, 58),
    (3793, 3553, 59), (3797, 3553, 60), (3801, 3553, 61), (3805, 3553, 62), (3809, 3553, 63), (4015, 5, 0),
    (4016, 5, 1), (4017, 5, 2), (4018, 5, 3), (4019, 5, 4), (4020, 5, 5), (4021, 5, 6), (4022, 5, 7),
    (4023, 5, 8), (4024, 5, 9), (4025, 5, 10), (4026, 5, 11), (4027, 5, 12), (4028, 5, 13), (4029, 5, 14),
    (4030, 5, 15), (4031, 5, 16), (4032, 5, 17), (4033, 5, 18), (4034, 5, 19), (4035, 5, 20), (4036, 5, 21),
    (4037, 5, 22), (4038, 5, 23), (4039, 5, 24), (4040, 5, 25), (4041, 5, 26), (4042, 5, 27), (4043, 5, 28),
    (4044, 5, 29), (4045, 5, 30), (4046, 5, 31), (4047, 5, 32), (4048, 5, 33), (4049, 5, 34), (4050, 5, 35),
    (4051, 5, 36), (4052, 5, 37), (4053, 5, 38), (4054, 5, 39), (4055, 5, 40), (4056, 5, 41), (4057, 5, 42),
    (4058, 5, 43), (4059, 5, 44), (4060, 5, 45), (4061, 5, 46), (4062, 5, 47), (4063, 5, 48), (4064, 5, 49),
    (4065, 5, 50), (4066, 5, 51), (4067, 5, 52), (4068, 5, 53), (4069, 5, 54)]

set_option maxRecDepth 200000 in
theorem vsStores_all : (storesOf 482 vsC).all (stTriple vsStoresT) = true := by decide +kernel

theorem vsStores_ok : ∀ a ∈ storesOf 482 vsC, stTriple vsStoresT a = true := fun a h =>
  List.all_eq_true.mp vsStores_all a h

/-- The runs' one definition no equation gives: `θ_0`'s store. -/
def secX : List Atom := [.load (.n 573) (.n 10) 0]

set_option maxRecDepth 200000 in
theorem chkRun_runP : chkRun (fun _ ↦ false) vsStoresT secX linkSec .nil = true := by decide +kernel

set_option maxRecDepth 200000 in
theorem chkRun_runR :
    chkRun (fun n ↦ n = 1049 || n = 1057 || n = 1058) vsStoresT secX linkSec .nil = true := by decide +kernel

/-- **The runs are sound on a forward valuation** whose `θ_0` store holds. -/
theorem linkSecRuns_of_good {rd : Reader} {w : ℕ → E} {args : List E} (ha : args.length = 6)
    (h573 : LoadHolds rd (vsVal rd w args (.n 10)) 0 (vsVal rd w args (.n 573))) :
    LinkSecRuns rd (vsVal rd w args) := by
  have hX : ∀ a ∈ secX, a.Holds rd (vsVal rd w args) := by
    intro a ha'
    simp only [secX, List.mem_singleton] at ha'
    subst ha'
    exact h573
  exact ⟨exec_evalG _ vsStoresT secX vsStores_ok hX (linkSec_good ha) chkRun_runP,
    exec_evalG _ vsStoresT secX vsStores_ok hX (linkSec_good ha) chkRun_runR⟩

/-! ## At the honest context -/

namespace VsCtx

variable {x : VsCtx}

/-- `rd0_runNe` from the placement and the buffers' sizes. -/
theorem rd0_runNe_of (hok : x.Ok) (hbw : x.bw.map List.length = vsAllocSz x.p) {j : ℕ} (hj : j < 24) (e13 : j ≠ 13)
    {k : ℕ} (hk : k < (vsAllocSz x.p).getD j 0) :
    x.rd0 (addressOfIndex (x.base j + k)) = some ((x.bw.getD j []).getD k 0) := by
  have ht : x.cur + (vsAllocSz x.p).sum < 2 ^ 60 + 2 ^ 14 := by
    obtain ⟨_, _, _, _, hN⟩ := frontNum_of_child hok.child
    have hp : x.p ≤ 32 := hN.hp
    have := hok.hcur; rw [vsAllocSz_sum]; omega
  have hl : x.bw.length = 24 := by rw [← List.length_map (f := List.length), hbw, vsAllocSz_length]
  have h13 := vsAllocSz_13 x.p
  have hbj : x.cur ≤ x.base j ∧ x.base j + (vsAllocSz x.p).getD j 0 ≤ x.cur + (vsAllocSz x.p).sum :=
    bases_getD_in x.cur (vsAllocSz x.p) j (by rw [vsAllocSz_length]; exact hj)
  have hb13 : x.cur ≤ x.base 13 ∧ x.base 13 + (vsAllocSz x.p).getD 13 0 ≤ x.cur + (vsAllocSz x.p).sum :=
    bases_getD_in x.cur (vsAllocSz x.p) 13 (by rw [vsAllocSz_length]; omega)
  have hjl : j < (bases x.cur (vsAllocSz x.p)).length := by rw [bases_length, vsAllocSz_length]; exact hj
  have hmem : (x.base j, x.bw.getD j []) ∈ vsRuns x.cur x.bw := by
    rw [vsRuns, hbw]
    have := List.getElem_mem (l := (bases x.cur (vsAllocSz x.p)).zip x.bw)
      (by rw [List.length_zip, bases_length, vsAllocSz_length, hl]; omega : j < _)
    rw [List.getElem_zip] at this
    rwa [base, List.getD_eq_getElem _ _ hjl, List.getD_eq_getElem _ _ (by omega)]
  have hsz : (x.bw.getD j []).length = (vsAllocSz x.p).getD j 0 := by
    rw [← hbw, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by rw [List.length_map]; omega),
      List.getElem_map]
  have hW := holdsWords_rdW (bases_zip_pairwise x.cur x.bw) (fun q hq => by
    have := bases_zip_in x.cur x.bw q hq; rw [hbw] at this; omega) _ hmem k (by rw [hsz]; exact hk)
  have h2 := hW.2
  rw [Main.addr_ofK] at h2
  have e1 : x.rd1 (addressOfIndex (x.base j + k)) = some ((x.bw.getD j []).getD k 0) := by
    rw [List.getD_eq_getElem _ _ (by rw [hsz]; exact hk)]
    exact rd1_of_rdW h2
  rw [← e1]
  refine rdSet_of_not fun q hq he => ?_
  simp only [cells19, vsCells19, List.mem_map, List.mem_range] at hq
  obtain ⟨t, ht', rfl⟩ := hq
  simp only at he
  have := addr_inj (by omega) (by omega) he
  rcases Nat.lt_or_gt_of_ne e13 with hlt | hlt
  · have := bases_getD_lt x.cur (vsAllocSz x.p) j 13 hlt (by rw [vsAllocSz_length]; omega)
    simp only [base] at *
    omega
  · have := bases_getD_lt x.cur (vsAllocSz x.p) 13 j hlt (by rw [vsAllocSz_length]; omega)
    simp only [base] at *
    omega

/-- `.n 10` points at buffer `4`. -/
theorem ptr10 (hret : CausalRule x.ret) : x.σ0 (.n 10) = ptrAt (x.base 4) := by
  have e := vsW_alloc (rd1 := x.rd1) (args := x.args) (cur := x.cur) (p := x.p) rfl hret (j := 4) (by omega)
  rw [vsAllocIdx_getD (by norm_num : 4 < 18)] at e
  exact (vsW0_good (rd0 := x.rd0) (w := x.w) rfl
    (by simp [vsW0, vsW0a] : Atom.hint (.alloc (.n (4 + 6)) 153) ∈ vsW0)).trans e

/-- `θ_0`'s store into `.n 10` holds on the evaluation memory. -/
theorem store573 (hok : x.Ok) (hret : CausalRule x.ret) (hbw : x.bw.map List.length = vsAllocSz x.p)
    (hb4 : (x.bw.getD 4 [])[0]? = some (x.w 573)) :
    LoadHolds x.rd0 (x.σ0 (.n 10)) 0 (x.σ0 (.n 573)) := by
  have ha : x.args.length = 6 := rfl
  have r6 : ∀ v ∈ [V.n 573, .n 574, .n 575, .n 576, .n 577, .n 578, .n 579, .n 580], x.σ0 v = x.w v.idx :=
    vsVal_retC (rd0 := x.rd0) (w := x.w) ha vsC6_eq
  have e573 : x.σ0 (.n 573) = x.w 573 := r6 (.n 573) (by simp)
  rw [ptr10 hret, e573]
  refine ⟨(isInK_iff _).mpr ⟨_, rfl⟩, ?_⟩
  rw [show (ptrAt (x.base 4)).limb 0 * addressOfIndex 0 = addressOfIndex (x.base 4 + 0) by
    simp [ptrAt, addressOfIndex], rd0_runNe_of hok hbw (by norm_num) (by norm_num)
    (by rw [show (vsAllocSz x.p).getD 4 0 = 153 from rfl]; norm_num)]
  rw [List.getD_eq_getElem?_getD, hb4, Option.getD_some]

/-- **The link section's runs are sound at the honest context** (`linkSecStatementRun`'s hypothesis in place of
every atom of the section holding). -/
theorem linkSecAtoms_honest (hok : x.Ok) (hret : CausalRule x.ret) (hbw : x.bw.map List.length = vsAllocSz x.p)
    (hb1 : x.Bw1) : LinkSecRuns x.rd0 x.σ0 :=
  linkSecRuns_of_good (rd := x.rd0) (w := x.w) (args := x.args) rfl (store573 hok hret hbw hb1.b4)

/-- The overlay's words are the stored values on `σ0`. -/
theorem cells19_σ0 (hf : VsFresh x.rd1 x.rd0 x.w x.args) {k : ℕ} (hk : k < 12) :
    (x.cells19.map Prod.snd).getD k 0 = x.σ0 (.n (Link.Arith.shiftStores.getD k (0, 0)).2) := by
  have ha : x.args.length = 6 := rfl
  have hv : tIdx vsRcs (vs19Src.getD k 0) = false := by interval_cases k <;> decide +kernel
  have hs : (Link.Arith.shiftStores.getD k (0, 0)).2 = vs19Src.getD k 0 := by interval_cases k <;> rfl
  have e1 : x.σ0 (.n (vs19Src.getD k 0)) = vsVal x.rd0 x.w x.args (.n (vs19Src.getD k 0)) := rfl
  rw [hs, e1, cells19, vsCells19_getD _ _ hk, vsVal_congr (v := .n (vs19Src.getD k 0)) ha hf hv]

set_option maxHeartbeats 4000000 in
/-- **`LinkSecVals` from the section's runs**, its reads (`IRReads` at `tailIn` of the native values) and the
overlay's fresh loads. -/
theorem linkSecVals_of_runs {L : LinkNat} {link : LinkEnd} (hL : L.Ok x.lay x.nF x.c.freshClaim link)
    (htab : x.lay.tables = tables) (hlb : x.lay.logBytecode = 19) (hf : VsFresh x.rd1 x.rd0 x.w x.args)
    (hT : LinkSecRuns x.rd0 x.σ0)
    (hr : Link.Arith.IRReads x.rd0 x.σ0 (tailIn x.lay L.chunks (L.theta0 x.lay x.nF) (L.drawn x.lay x.nF)
      (L.r x.lay x.nF) L.m1 (L.fresh x.lay x.nF) x.c.freshClaim.values (L.chi x.lay x.nF) (L.qPoint x.lay x.nF)
      L.msg)) :
    LinkSecVals x L := by
  have hs := x.natTailShape hL htab
  have hst := Link.Arith.linkSecStatementRun x.rd0 x.σ0 x.lay
    L.chunks (L.theta0 x.lay x.nF) (L.drawn x.lay x.nF) (L.r x.lay x.nF) L.m1 (L.fresh x.lay x.nF)
    x.c.freshClaim.values (L.chi x.lay x.nF) (L.qPoint x.lay x.nF) L.msg hT hr hs hlb
  dsimp only at hst
  obtain ⟨-, -, -, -, -, -, h2846, -, h2890, -, h2891, hsh⟩ := hst
  have hrow := Link.Arith.rowIdentity x.lay L.chunks (L.theta0 x.lay x.nF) (L.drawn x.lay x.nF) (L.r x.lay x.nF)
    L.m1 (L.fresh x.lay x.nF) x.c.freshClaim.values (L.chi x.lay x.nF) (L.qPoint x.lay x.nF) L.msg hs
  dsimp only at hrow
  have hR12 : (natRow x L).shifts.length = 12 := by
    unfold natRow
    rw [← hrow.2.1]
    simp [Link.Arith.gShifts]
  have hc12 : (x.cells19.map Prod.snd).length = 12 := by simp [VsCtx.cells19, vsCells19]
  refine ⟨h2846, h2891, h2890, List.ext_getElem (hc12.trans hR12.symm) fun i h1 h2 => ?_⟩
  have e := cells19_σ0 hf (k := i) (by omega)
  rw [hsh i (by omega), List.getD_eq_getElem _ _ h1] at e
  rw [e]
  exact Link.Arith.getD_eq_getElem' h2

end VsCtx

end
end LeanVM.Guest.B1.VsC
