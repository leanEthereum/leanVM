/-
  LeanVM.Guest.B1.VerifySub.LanesK

  The output lanes' claims of `verify_sub`'s table phase: at the table sumcheck's point cut to
  the `KECCAK` table's height, their values at `col_eval_words·g^107`.
-/

module

public import LeanVM.Guest.B1.VerifySub.SoundLib
public import LeanVM.Guest.B1.KeccakGkr.VkStep

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Carried sponges -/

theorem RunsTo.carrier {α : Type} {p : VerifierProgram α} {s s' : Fs} {xs : List E} {a : α}
    (h : RunsTo p s xs a s') {sp : Sponge} (hs : s.Carries sp) : ∃ sp', s'.Carries sp' := by
  obtain ⟨sp', h', -⟩ := h sp hs [] [] []
  exact ⟨sp', h'⟩

theorem carrier_of_squeeze {s s' : Fs} {c : E} (h : s.squeeze = (c, s')) :
    ∃ sp : Sponge, s'.Carries sp := by
  refine ⟨⟨s.perm, []⟩, ?_⟩
  have e : s' = s.squeeze.2 := by rw [h]
  rw [e]
  exact ⟨rfl, rfl⟩

/-! ## Heights -/

theorem le_foldl_max : ∀ (l : List ℕ) (acc : ℕ), acc ≤ l.foldl max acc
  | [], _ => le_rfl
  | x :: l, acc => le_trans (le_max_left acc x) (le_foldl_max l (max acc x))

theorem mem_le_foldl_max : ∀ {l : List ℕ} {x : ℕ} (acc : ℕ), x ∈ l → x ≤ l.foldl max acc
  | y :: l, x, acc, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact le_trans (le_max_right acc x) (le_foldl_max l (max acc x))
    · exact mem_le_foldl_max (max acc y) h

theorem layoutOf_heights (bytecode : List K) (m : ℕ) (rowsN : List ℕ) :
    (Tables.layoutOf bytecode m rowsN).tableLogHeights = Tables.tableHeightsOf rowsN := rfl

/-- The GKR's capacity: `verify_bus_gkr`'s first five return words. -/
theorem VsFront.capG_eq {bytecode : List K} {C : CallRel} {rd : Reader} {σ : Val}
    (F : VsFront bytecode C rd σ) :
    F.capG = [σ (.n 626), σ (.n 627), σ (.n 628), σ (.n 629), σ (.n 630)] := by
  have h := F.hretG
  rw [show [σ (.n 626), σ (.n 627), σ (.n 628), σ (.n 629), σ (.n 630), σ (.n 631), σ (.n 632),
    σ (.n 633), σ (.n 634)] = ([σ (.n 626), σ (.n 627), σ (.n 628), σ (.n 629), σ (.n 630)] ++
      [σ (.n 631)]) ++ [σ (.n 632), σ (.n 633), σ (.n 634)] from rfl] at h
  obtain ⟨h1, -⟩ := List.append_inj' h (by rw [F.hvL]; rfl)
  exact (List.append_inj' h1 rfl).1.symm

/-- The `KECCAK` table's height. -/
abbrev vsTau (rowsN : List ℕ) : ℕ := (Tables.tableHeightsOf rowsN).getD 5 0

/-- The claimed fixed polynomial value at the bus's bytecode point. -/
def vsFixed (σ : Val) (point : List E) : BytecodeClaim :=
  ⟨point.take 19 ++ vsAlphas σ, σ (.n 643)⟩

/-- **The output lanes**: their claims are on `KECCAK`'s output columns at one point, the table
sumcheck's point `chis` (at `chi`) cut to the table's height `τ ≤ |chis|`, and their values are
at `col_eval_words·g^107` (claims `112 .. 136`, read in place: `col_eval_words` holds claims `5 .. 163`). -/
theorem vs_lanes {bytecode : List K} (hbl : bytecode.length = 2 ^ 23) {C : CallRel} {rd : Reader}
    {σ : Val} (F : VsFront bytecode C rd σ) :
    ∃ chis : List E, ReadsAt rd (σ (.n 635)) chis ∧ vsTau F.rowsN ≤ chis.length ∧
      (lanesOf F.claims).map (·.column) = keccakOutputColumns ∧
      (∀ c ∈ lanesOf F.claims, c.point = chis.take (vsTau F.rowsN)) ∧
      ReadsAt rd (σ (.n 645) * gen ^ 107) ((lanesOf F.claims).map (·.value)) ∧
      (lanesOf F.claims).length = 25 := by
  have hctx := F.hctx
  simp only [Tables.TCtx] at hctx
  obtain ⟨chis, -, -, hchi, -, -, hcl, hcol, hpts⟩ := hctx
  obtain ⟨hlanes, -⟩ := lanes_eq hcol
  -- the table phase's points
  obtain ⟨sp4, hs4⟩ := carrier_of_squeeze F.hbeta
  obtain ⟨sp5, hs5⟩ := RunsTo.carrier F.hrunG hs4
  rw [F.capG_eq] at hs5
  have hcl' : F.claims.length = 167 := hcl
  have hτdef : vsTau F.rowsN = (Tables.tableHeightsOf F.rowsN).getD 5 0 := rfl
  have hrunT := F.hrunT (claimedBytecodeValue (vsFixed σ F.r.2.1)) (by
    rw [logBytecode_eq hbl]; exact bytecodeAt_claimed bytecode _ _)
  obtain ⟨pt, hptL, hpt⟩ := RunsTo.always hrunT hs5 (tablesSeg_lanes _ _ _ _ _ _ _)
  rw [layoutOf_heights, show opKeccak = 5 from rfl] at hpt
  rw [layoutOf_heights] at hptL
  have hτpt : vsTau F.rowsN ≤ pt.length := by
    rw [hptL]
    exact mem_le_foldl_max 0 (getD_mem' (by rw [tableHeights_length _ F.hrowsL]; omega))
  -- a lane's point
  have hlane : ∀ i < 25, (F.claims[112 + i]?.map (·.point)) = some (chis.take (vsTau F.rowsN)) ∧
      (chis.take (vsTau F.rowsN)).length = vsTau F.rowsN := by
    intro i hi
    have hlt : 112 + i < F.claims.length := by rw [hcl']; omega
    have hmem : F.claims[112 + i] ∈ (F.claims.drop 112).take 25 := by
      rw [List.mem_iff_getElem]
      exact ⟨i, by simp; omega, by simp⟩
    have hout : F.claims[112 + i].column ∈ keccakOutputColumns := by
      apply claimColumns_lanes
      rw [← hcol, ← List.map_drop, ← List.map_take]
      exact List.mem_map_of_mem hmem
    have e1 := hpt _ (List.getElem_mem hlt) hout
    obtain ⟨-, -, h5, -⟩ := hpts (112 + i) F.claims[112 + i].point (by simp [hlt])
    have e2 := h5 (by omega) (show 112 + i < 164 by omega)
    have hlen : F.claims[112 + i].point.length = vsTau F.rowsN := by
      rw [e1, List.length_take, ← hτdef]; omega
    rw [hlen] at e2
    refine ⟨by simpa [List.getElem?_eq_getElem hlt] using congrArg some e2, by rw [← e2, hlen]⟩
  have hτ : vsTau F.rowsN ≤ chis.length := by
    have := (hlane 0 (by omega)).2
    rw [List.length_take] at this
    omega
  refine ⟨chis, hchi, hτ, ?_, ?_, ?_, ?_⟩
  · rw [hlanes, List.map_take, List.map_drop, hcol]
    exact claimColumns_lanes_eq
  · intro c hc
    rw [hlanes, List.mem_iff_getElem] at hc
    obtain ⟨i, hi, rfl⟩ := hc
    have hi' : i < 25 := by simp at hi; omega
    have := (hlane i hi').1
    simp only [List.getElem_take, List.getElem_drop]
    rw [List.getElem?_eq_getElem (by rw [hcl']; omega)] at this
    simpa using this
  · rw [hlanes]
    intro k hk
    have hk' : k < 25 := by simp [hcl'] at hk; omega
    rw [loadHolds_mul_gen_pow]
    have e2 : Tables.nPooled = 164 := rfl
    have e3 : Tables.nBusClaims = 5 := rfl
    have := F.hcew (107 + k) (by simp [hcl']; omega)
    simp only [List.getElem_map, List.getElem_take, List.getElem_drop] at this ⊢
    convert this using 3
    omega
  · rw [hlanes]; simp [hcl']

end
end LeanVM.Guest.B1.VerifySub
