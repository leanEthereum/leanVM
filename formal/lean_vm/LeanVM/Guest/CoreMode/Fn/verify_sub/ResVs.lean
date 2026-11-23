/-
  LeanVM.Guest.CoreMode.Fn.verify_sub.ResVs

  `verify_sub`'s exponent facts (`Res.vsFacts`) at its honest frames, and its residuals in their
  families (`Res.vsB`).
-/

module

public import LeanVM.Guest.Mode.ResFam
public import LeanVM.Guest.CoreMode.Fam.EfDefs
public import LeanVM.Guest.Value.Bits
public import LeanVM.Guest.CoreMode.Fn.verify_keccak.ResSt
public import LeanVM.Guest.CoreMode.Fn.verify_keccak.ResVk
public import LeanVM.Guest.CoreMode.Fam.Kid
public import LeanVM.Guest.CoreMode.Fn.verify_tables.ResVtL
public import LeanVM.Guest.CoreMode.Fam.ResCld
public import LeanVM.Guest.CoreMode.Fam.SubDefs
public import LeanVM.Guest.CoreMode.Fn.keccak_layer.ResStB
public import LeanVM.Guest.B1.VerifySub.Lanes
public import LeanVM.Guest.B1.KeccakGkr.VkHolds
public import LeanVM.Guest.B1.Bits.Grind
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«verify_sub»

/-!
# `verify_sub`'s frame cells and values

`vs_cells`: the frame cells of `verify_sub`'s values `25`, `278` and `71`, inside its frame.
`vs_valsI`: at an honest instance of `verify_sub`, its front (`B1.VerifySub.vs_front`) gives the
tables' log-heights, the stack's log, the bus depth and the cursors its reads take.
-/

namespace LeanVM.Guest.Res

open LeanVM.Guest LeanVM.Guest.Core

@[expose] public section

/-- **`verify_sub`'s exponent facts**: the tables' log-heights `dims[1..6]` (`[[75]·g^t]`), the
keccak table's (`t = 6`) at least `9` and at most `24`; the stack's log less `20` (`[202]`); the bus
depth (`log2_ceil`'s return, `[[168]·g^4]`); the table sumcheck's depth (`verify_tables`' return,
`[[499]·g^29]`), at least the keccak table's; the stack's log (`[[199]·g^4]`); the cursors
`verify_bus_gkr`, `verify_tables` and `verify_keccak` return, in the stream `[27]`. -/
def vsFacts : EFacts where
  pows := ((List.range 5).map fun t ↦ (.hp 75 (t + 1), 0, 30)) ++
    [(.hp 75 6, 9, 24), (.fr 202, 0, 10), (.hp 168 4, 20, 33), (.hp 499 29, 9, 33), (.hp 199 4, 20, 30)]
  les := [(.hp 75 6, .hp 499 29, 0), (.hp 199 4, .fr 202, 20)]
  curs := [(.hp 485 17, .fr 27, 14), (.hp 499 28, .fr 27, 49), (.hp 512 20, .fr 27, 207)]

/-- **A residual of `verify_sub` its exponent facts take.** -/
noncomputable def vsB (j : ℕ) (x : Mode.Res) : Bool :=
  (coreOf j).name == name% «verify_sub» && efFamB vsFacts x

end

end LeanVM.Guest.Res

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Mode LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.B1
open LeanVM.Guest.B2C (idxOf fsN cellJ)
open LeanVM.Guest.Bridge (FnAl)
open LeanVM.Guest.Res (EFacts vsFacts vsB topAtoms)
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Prover.Exec

public section

/-! ## The body's facts -/

section

variable {A : String → FnAl} {r : Ref} {K : Mode.Cert} {i : ℕ} {e : Bridge.Ent} {j : ℕ}

/-- **`verify_sub`'s values at an honest instance**: the tables' log-heights `hs` in `dims`, the stack's log `sl`, the
bus depth `d`, the table sumcheck's depth `n`, the cursors past the bus's GKR walk, the tables' segment and
`verify_keccak`, `gK + 207` words at most into the stream. -/
theorem vs_valsI (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T) {σ : Core.Val}
    {bufs : List ℕ} {kids : List Tree} (hIt : I.t = .node name% «verify_sub» σ bufs kids) :
    ∃ (hs : List ℕ) (lm sl d n gG gT gK : ℕ),
      hs.length = 6 ∧ (∀ h ∈ hs, h < 31) ∧ 9 ≤ hs.getD 5 0 ∧ hs.getD 5 0 ≤ 24 ∧
      ReadsAt r.img.read (σ (.n (val% «verify_sub» "dims_g"))) (gen ^ lm :: hs.map (gen ^ ·)) ∧
      20 ≤ sl ∧ sl ≤ 30 ∧ σ (.n (val% «verify_sub» "size_sel")) = gen ^ (sl - 20) ∧ σ (.n (val% «verify_sub» "gmv")) = gen ^ sl ∧
      20 ≤ d ∧ d < 34 ∧ σ (.n (val% «verify_sub» "g_bus_mu")) = gen ^ d ∧
      hs.getD 5 0 ≤ n ∧ n ≤ d ∧ σ (.n (val% «verify_sub» "g_zc_n")) = gen ^ n ∧
      σ (.n (val% «verify_sub» "cursor@2")) = σ (.n (val% «verify_sub» "stream")) * gen ^ gG ∧ σ (.n (val% «verify_sub» "cursor@3")) = σ (.n (val% «verify_sub» "stream")) * gen ^ gT ∧
      σ (.n (val% «verify_sub» "cursor@4")) = σ (.n (val% «verify_sub» "stream")) * gen ^ gK ∧ gG ≤ gT ∧ gT ≤ gK ∧ gK + 207 ≤ 8192 := by
  have hfj : coreProgram.find? name% «verify_sub» = some (fn% «verify_sub») := VerifySub.find_vs
  obtain ⟨args, rets, hv⟩ := inst_valid' hr hI hIt
  obtain ⟨-, hb⟩ := Res.holds_of_valid Res.fs_pos hv hfj
  rw [VerifySub.vs_body] at hb
  have hκ : r.κ ≤ 28 := logMemorySize_le_28 (e := r.exec) hr.size
  obtain ⟨hexp, hwin⟩ := carryQ_all hr I hI _ σ bufs kids hIt _ hfj (name% «verify_sub», 4, .tab)
    (by decide) rfl (.n (val% «verify_sub» "g_squares")) (by rw [VerifySub.vs_params]; rfl)
  obtain ⟨⟨F⟩, -⟩ := VerifySub.vs_front (by omega) r.img (fun _ _ _ h ↦ Res.KidRel.rel h)
    (bytecode := List.replicate (2 ^ 23) 0) List.length_replicate hexp hwin hb
  have hκw := VerifySub.winTab_kappa (by omega) r.img hwin
  -- the words read before each cursor
  obtain ⟨sp, hsp⟩ := front_carried F
  obtain ⟨hlG, sp', hsp'⟩ := runsTo_reads (reads_gkrPhase _) F.hG hsp
  have hhl : ∀ h ∈ (Tables.layoutOf (List.replicate (2 ^ 23) 0) F.logMem F.rowsN).tableLogHeights,
      h ≤ 30 := by
    rw [VerifySub.layoutOf_heights]
    intro h hh'
    have := F.hh31 h hh'
    omega
  have hRT := reads_tablesSeg (claimedBytecodeValue ⟨F.bus.bytecodePoint, σ (.n (val% «verify_sub» "bc_value"))⟩)
    (fun w p v ↦ Child.reads_claimedBytecodeValue ⟨F.bus.bytecodePoint, σ (.n (val% «verify_sub» "bc_value"))⟩ w p v) _ hhl F.pi F.weights
    (σ (.n (val% «verify_sub» "nxt[0]@19"))) F.r.2.1 F.r.2.2
  obtain ⟨hlT, sp'', hsp''⟩ := runsTo_reads hRT F.hT hsp'
  generalize (List.replicate (2 ^ 23) 0 : List LeanVM.Parameters.K) = bc at F hhl
  -- the tables' context
  obtain ⟨chis, hbpR, hgmu, hchi, hgzc, hchiL, -, hcol, hpts⟩ := F.hctx
  have hpts' : ∀ j (p : List E), (F.claims.map (·.point))[j]? = some p →
      (j < Tables.nPooled → p.length = Tables.claimLowDim F.logMem (Tables.tableHeightsOf F.rowsN) j) ∧
      (Tables.nBusClaims ≤ j → j < Tables.nPooled → p = chis.take p.length) :=
    fun j p hp ↦ ⟨(hpts j p hp).1, (hpts j p hp).2.2.1⟩
  obtain ⟨-, -, -, hl25, hlR⟩ := VerifySub.lanes_facts F.hcl hcol hpts' F.hcew
  have hτc : ((Tables.tableHeightsOf F.rowsN).getD 5 0) ≤ chis.length := by
    have h105 : 105 < (F.claims.map (·.point)).length := by simp [F.hcl]
    obtain ⟨hl, -, ht, -⟩ := hpts 105 _ (List.getElem?_eq_getElem h105)
    have hsrc : Tables.claimKappaSrc.getD 105 0 = 7 := by decide +kernel
    have hcd : Tables.claimLowDim (Tables.layoutOf (bc) F.logMem F.rowsN).logMemory
        (Tables.layoutOf (bc) F.logMem F.rowsN).tableLogHeights 105 =
          ((Tables.tableHeightsOf F.rowsN).getD 5 0) := by
      rw [VerifySub.layoutOf_heights]
      unfold Tables.claimLowDim
      rw [hsrc]
      simp [Tables.claimKappaAdj]
    have e1 := hl (by decide)
    have e2 := congrArg List.length (ht (by decide) (by decide))
    rw [hcd] at e1
    rw [List.length_take] at e2
    omega
  have hτ9 := VerifySub.tau_ge F.hrowsL
  have hτ24 := VerifySub.tau_le_of_kappasBelow (VerifySub.tableHeights_length _ F.hrowsL) F.hKB
  -- `verify_keccak`
  have hK := VerifySub.verify_keccak_holds (by omega) hκw r.img _ _
    (Res.KidRel.rel F.hkc)
  obtain ⟨xsK, op, point, slices, word, s', -, hrunK, -, -, -, -, -, -, -, hretK⟩ :=
    hK (by rw [F.h589]; exact VerifySub.winTabs_of hwin) ((Tables.tableHeightsOf F.rowsN).getD 5 0) chis _ hτ9
      (by omega) F.h583 hτc hchi hl25 (by rw [F.h587]; exact hlR)
  obtain ⟨-, hK2⟩ := List.append_inj' (show [σ (.n (val% «verify_sub» "fs0@5")), σ (.n (val% «verify_sub» "fs1@5")), σ (.n (val% «verify_sub» "fs2@5")), σ (.n (val% «verify_sub» "fs3@5")),
    σ (.n (val% «verify_sub» "fs4@5"))] ++ [σ (.n (val% «verify_sub» "cursor@4")), σ (.n (val% «verify_sub» "keccak_word"))] = _ from hretK) rfl
  simp only [List.cons.injEq, and_true] at hK2
  obtain ⟨e595, -⟩ := hK2
  obtain ⟨hlK, -⟩ := runsTo_reads (Child.reads_verifyKeccak _ _ _ (by simp only [List.length_take]; omega)) hrunK hsp''
  -- the bus depth
  have hbusL : F.bus.point.length = VerifySub.busDepth (Tables.layoutOf (bc) F.logMem F.rowsN) := by
    have := hgmu.symm.trans F.h253
    exact Value.gen_pow_inj (by have := VerifySub.mem_size_le (by omega) r.img hbpR; omega) (by have := F.hdep34; omega) this
  have hgk := Child.gkrReads_le (VerifySub.busDepth (Tables.layoutOf (bc) F.logMem F.rowsN))
    (by have := F.hdep34; omega)
  have hroom : 13 + (2 + Child.gkrReadsBound) + (busRestReads + Child.tableReads) + Child.keccakReads 27 + 207
      ≤ 8192 := by decide
  refine ⟨Tables.tableHeightsOf F.rowsN, F.logMem, _, _, chis.length, 13 + F.xsG.length,
    13 + F.xsG.length + F.xsT.length, 13 + F.xsG.length + F.xsT.length + xsK.length,
    VerifySub.tableHeights_length _ F.hrowsL, fun h hh ↦ F.hh31 h hh, hτ9, hτ24, F.hdims, F.hst20, F.hst30,
    F.h278, F.h276, F.hdep20, F.hdep34, F.h253, hτc, by omega, hgzc, ?_, ?_, ?_, by omega, by omega, by omega⟩
  · rw [F.h567, F.h320, F.h312]
    simp only [mul_assoc, ← pow_add]
  · rw [F.h578, F.h567, F.h320, F.h312]
    simp only [mul_assoc, ← pow_add]
  · rw [e595, F.h578, F.h567, F.h320, F.h312]
    simp only [mul_assoc, ← pow_add]

end

end

end LeanVM.Guest.EndExec
