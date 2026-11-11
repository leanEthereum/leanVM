/-
  LeanVM.Guest.B1.VerifySub.H.Data

  An honest child's data, as `verify_sub`'s callees take it: the bus depth, the GKR's run from a
  capacity, `verify_tables`' honest data (B1-c's `VtHonest`, `Ok`, `VtShape`), the claimed
  bytecode point, the output lanes and the Keccak reduction's run.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Bounds
public import LeanVM.Guest.B1.VerifySub.H.Mid
public import LeanVM.Guest.B1.VerifySub.H.Lanes
public import LeanVM.Guest.B1.VerifySub.LanesK

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

theorem squeezeN_len : ∀ (n : ℕ) (s : Fs), (s.squeezeN n).1.length = n
  | 0, _ => rfl
  | n + 1, s => by simp [Fs.squeezeN, squeezeN_len n]

theorem vtPushPad_tabs : Tables.vtPushPadData.map (·.2.1) =
    List.replicate 5 0 ++ List.replicate 5 1 ++ List.replicate 3 2 ++ List.replicate 5 3 ++
      List.replicate 5 4 ++ List.replicate 28 5 := by decide

theorem vtCountPad_tabs : Tables.vtCountPadData.map (·.2.1) =
    List.replicate 4 0 ++ List.replicate 4 1 ++ List.replicate 2 2 ++ List.replicate 4 3 ++
      List.replicate 4 4 ++ List.replicate 27 5 := by decide

/-- The push side's sizes total the push total. -/
theorem vtSizesP_sum (lm : ℕ) (rows : List ℕ) (hr : rows.length = 6) :
    ((Tables.vtSizesP lm (Tables.vtHt rows)).map (2 ^ ·)).sum =
      pushTotal lm (Tables.tableHeightsOf rows) := by
  have hsl := tableHeights_length rows hr
  have e : Tables.vtSizesP lm (Tables.vtHt rows) = [0, lm, 19] ++
      (Tables.vtPushPadData.map (·.2.1)).map (Tables.vtHt rows) := by
    simp only [Tables.vtSizesP, List.map_map]; rfl
  rw [e, vtPushPad_tabs]
  match hh : Tables.tableHeightsOf rows, hsl with
  | [h0, h1, h2, h3, h4, h5], _ =>
    rw [pushTotal_eq]
    simp only [List.map_append, List.map_replicate, List.sum_append, List.sum_replicate,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, smul_eq_mul, Tables.vtHt, hh,
      List.getD_cons_succ, List.getD_cons_zero]
    ring

/-- The count side's sizes total at most the push total. -/
theorem vtSizesC_sum (lm : ℕ) (rows : List ℕ) (hr : rows.length = 6) :
    ((Tables.vtSizesC (Tables.vtHt rows)).map (2 ^ ·)).sum ≤
      pushTotal lm (Tables.tableHeightsOf rows) := by
  have hsl := tableHeights_length rows hr
  have e : Tables.vtSizesC (Tables.vtHt rows) =
      (Tables.vtCountPadData.map (·.2.1)).map (Tables.vtHt rows) := by
    simp only [Tables.vtSizesC, List.map_map]; rfl
  rw [e, vtCountPad_tabs]
  match hh : Tables.tableHeightsOf rows, hsl with
  | [h0, h1, h2, h3, h4, h5], _ =>
    rw [pushTotal_eq]
    simp only [List.map_append, List.map_replicate, List.sum_append, List.sum_replicate,
      smul_eq_mul, Tables.vtHt, hh,
      List.getD_cons_succ, List.getD_cons_zero]
    have := Nat.two_pow_pos lm
    omega

/-- Each height is at most the bus depth. -/
theorem height_le_depth (lm : ℕ) {hs : List ℕ} (hl : hs.length = 6) {t : ℕ} (ht : t < 6) :
    hs.getD t 0 ≤ log2Ceil (pushTotal lm hs) ∧ lm ≤ log2Ceil (pushTotal lm hs) := by
  match hs, hl with
  | [h0, h1, h2, h3, h4, h5], _ =>
    have hp := pushTotal_eq lm h0 h1 h2 h3 h4 h5
    have := Nat.two_pow_pos lm
    refine ⟨Tables.tb_le_log2Ceil_of_two_pow_le ?_, Tables.tb_le_log2Ceil_of_two_pow_le (by omega)⟩
    interval_cases t <;> simp only [List.getD_cons_zero, List.getD_cons_succ] <;> omega

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

/-- The tables' heights. -/
def hs : List ℕ := Tables.tableHeightsOf S.rowsN

/-- The bus depth. -/
def μ : ℕ := log2Ceil (pushTotal S.logMem S.hs)

/-- The capacity the bus's GKR starts from. -/
def capS : List E := S.s3.squeeze.2.cap

/-- `β`. -/
def β : E := S.s3.squeeze.1

/-- The bus point. -/
def point : List E := S.rG.2.1

/-- The GKR's three values. -/
def vals : List E := S.rG.2.2

/-- The `KECCAK` table's height. -/
def τ : ℕ := S.hs.getD 5 0

/-- **`verify_tables`' honest data.** -/
noncomputable def H : Tables.VtHonest :=
  Tables.vtHOf bytecode S.logMem (statementDigest seed c.statement) S.alphas S.point S.vals S.β S.rowsN S.s5.cap
    (claimedBytecodeValue c.freshClaim) c.freshClaim.bytecodeValue S.xsT S.bus S.claims S.s6.cap

theorem hs_length : S.hs.length = 6 := tableHeights_length _ S.hrowsL

theorem stack32 : (Tables.layoutOf bytecode S.logMem S.rowsN).stackLog ≤ 32 := by
  rw [← S.hlayout]; exact S.hmu32

theorem hh33 (hbl : bytecode.length = 2 ^ 23) : ∀ h ∈ S.hs, h < 33 :=
  vsH_heights hbl S.hrowsL S.stack32

theorem μ_eq (hbl : bytecode.length = 2 ^ 23) :
    (busLayout [0, S.layout.logMemory, S.layout.logBytecode] S.layout.push).depth = S.μ := by
  rw [S.hlayout]; exact pushDepth_eq hbl S.logMem S.rowsN S.hrowsL

theorem μ_bounds (hbl : bytecode.length = 2 ^ 23) : 20 ≤ S.μ ∧ S.μ ≤ 32 :=
  ⟨depth_ge S.hs_length, (vsH_depth hbl S.hrowsL S.hlm1 S.stack32).1⟩

theorem pushTotal_lt (hbl : bytecode.length = 2 ^ 23) : pushTotal S.logMem S.hs < 2 ^ 34 := by
  have := (vsH_depth hbl S.hrowsL S.hlm1 S.stack32).2
  show pushTotal S.logMem S.hs < 2 ^ 34
  unfold ChildSegs.hs
  omega

theorem capS_carries : ∃ sp, (⟨S.capS, []⟩ : Fs).Carries sp :=
  carrier_of_squeeze (s := S.s3) (c := S.s3.squeeze.1) rfl

theorem capS_length : S.capS.length = 5 := rfl

/-- **The bus's GKR from its capacity**, ending on a permutation's capacity. -/
theorem runG' (hbl : bytecode.length = 2 ^ 23) :
    RunsTo (Tables.gkrPhase S.μ) ⟨S.capS, []⟩ S.xsG S.rG ⟨S.s5.cap, []⟩ ∧
      S.s5 = ⟨S.s5.cap, []⟩ ∧ S.point.length = S.μ ∧ (∃ K, S.s5.cap = capOf K) := by
  have h := S.runG
  rw [S.μ_eq hbl] at h
  have h' : RunsTo (Tables.gkrPhase S.μ) ⟨S.capS, []⟩ S.xsG S.rG S.s5 := h
  obtain ⟨K, hK⟩ := gkr_capOf (by have := (S.μ_bounds hbl).1; omega) h' S.capS_carries
  have he : S.s5 = ⟨S.s5.cap, []⟩ := by rw [hK]
  refine ⟨he ▸ h', he, ?_, K, by rw [hK]⟩
  obtain ⟨-, -, -, -, -, -, hr, hpl⟩ := Tables.gk_walk h' S.capS_carries
  show S.rG.2.1.length = S.μ
  rw [hr]; exact hpl

theorem s5_carries (hbl : bytecode.length = 2 ^ 23) : ∃ sp, (⟨S.s5.cap, []⟩ : Fs).Carries sp :=
  Tables.RunsTo.carries (S.runG' hbl).1 S.capS_carries

/-- **The claimed bytecode point** is the bus point's bytecode part and the challenges. -/
theorem fresh_eq (hbl : bytecode.length = 2 ^ 23) :
    c.freshClaim = ⟨S.point.take 19 ++ S.alphas, c.freshClaim.bytecodeValue⟩ := by
  have h := S.runT
  have hp := claimed_point h (by rw [(S.runG' hbl).2.1]; exact S.s5_carries hbl)
  rw [S.hlayout, logBytecode_eq hbl] at hp
  have hp' : c.freshClaim.bytecodePoint = S.point.take 19 ++ S.alphas := hp
  rw [← hp']

theorem bytecodeAt (hbl : bytecode.length = 2 ^ 23) :
    Tables.BytecodeAt (claimedBytecodeValue c.freshClaim) (Tables.layoutOf bytecode S.logMem S.rowsN).bytecode
      (S.point.take (Tables.layoutOf bytecode S.logMem S.rowsN).logBytecode ++ S.alphas)
      c.freshClaim.bytecodeValue := by
  rw [logBytecode_eq hbl, S.fresh_eq hbl]
  exact bytecodeAt_claimed _ _ _

/-- **`verify_tables`' honest data is the run's**, accepted. -/
theorem H_run (hbl : bytecode.length = 2 ^ 23) :
    S.H.Ok ∧ S.xsT = S.H.xs5 ++ S.H.xsR ++ S.H.evsT.flatten ∧ S.s6 = ⟨S.s6.cap, []⟩ ∧
      S.xsT.length = 5 + 3 * S.H.n + 159 := by
  have h := S.runT
  rw [S.hlayout, (S.runG' hbl).2.1] at h
  exact Tables.vtH_run S.hrowsL h (S.s5_carries hbl) (S.bytecodeAt hbl)

theorem H_rows : S.H.rows = S.rowsN := rfl
theorem H_lm : S.H.lm = S.logMem := rfl
theorem H_point : S.H.point = S.point := rfl
theorem H_f : S.H.f = S.s5.cap := rfl
theorem H_claims : S.H.claims = S.claims := rfl

end ChildSegs

end
end LeanVM.Guest.B1.VerifySub
