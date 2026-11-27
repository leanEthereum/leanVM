/-
  LeanVM.Guest.B1.KeccakGkr.VkCI

  `verify_keccak`'s callees, honestly: the copy loops, the openings' rounds, the twelve layers,
  each complete where `verify_keccak` places it.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCH
public import LeanVM.Guest.B1.KeccakGkr.LayerCPlaced
public import LeanVM.Guest.B1.KeccakGkr.CopyLoopIn
public import LeanVM.Guest.B1.KeccakGkr.PlainCompleteIn
public import LeanVM.Guest.Data.NameStrings

/-!
# The callees

For a `VkData` `D` with `D.Ok`, the caller's words `D.lin …` (the stream, the instance and
output coordinates, `z_vals`, the inputs' point, the slices) and the buffers' base `B`:

* `D.kids …`: the eighteen calls in order (`verify_keccak_loop0`, the twelve layers, the committed
  outputs' rounds, `verify_keccak_loop1`, the inputs' rounds, their opening's rounds,
  `verify_keccak_loop2`), each with its arguments, the caller's words it reads and what it returns;
  a layer's next claim's record sits in `verify_keccak`'s claim records, pointing into the layer's
  buffers, and the next layer reads them; `verify_keccak_loop2` copies the last claim's point out of
  the last layer's buffers.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory LeanVM.Guest.Lift
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr
open LeanVM.Guest.B1.Main (MemL RegionL)

@[expose] public noncomputable section

/-- `verify_keccak`'s loadless callees. -/
def vkKidS : List String := [name% «verify_keccak_loop0», name% «verify_keccak_loop1»,
    name% «verify_keccak_loop2», "keccak_plain_rounds__L6_L0",
  "keccak_plain_rounds__L4_L1"]

theorem vkKidS_pure : coreProgram.PureIn vkKidS := Tables.pureIn_of_pureInB (by decide +kernel)

theorem scalarCells_inj {x z : E} {t : ℕ} (h : Keccak.scalarCells x t = Keccak.scalarCells z t) :
    x = z := by
  simp only [Keccak.scalarCells, Prod.mk.injEq] at h
  exact h.1

namespace VkData

variable (D : VkData)

/-- The caller's words. -/
def lin (curE chiE olE zvE slE tbE : ℕ) : Main.Layout :=
  [(curE, D.xs), (chiE, D.chis), (olE, D.outs), (zvE, D.op), (zvE + qkeccakVarsCap, D.point),
    (slE, D.slices), (tbE, winTabWords)]

/-- The cursor after the layers. -/
def cL (curE : ℕ) : E := ptr (curE + D.lcur 12)

/-- The committed outputs' rounds' arguments and returns. -/
def oArgs (curE zvE tbE : ℕ) : List E :=
  D.L.2.cap ++ [0, 0, D.cL curE, D.committed, ptr zvE * gen ^ D.τ, ptr tbE]
def oRets (curE : ℕ) : List E := D.O.2.2.cap ++ [D.cL curE * gen ^ (2 * 6), D.O.2.1]

/-- The inputs' rounds' arguments and returns. -/
def iArgs (curE zvE tbE : ℕ) : List E :=
  D.O.2.2.cap ++ [(Keccak.scalarCells D.word dsObserve).1, (Keccak.scalarCells D.word dsObserve).2,
    D.cL curE * gen ^ (2 * 6) * gen, D.L.1.value, ptr zvE * gen ^ 39, ptr tbE]
def iRets (curE : ℕ) : List E := D.I.2.2.cap ++ [D.cL curE * gen ^ (2 * 6) * gen * gen ^ (2 * 4), D.I.2.1]

/-- The inputs' opening's rounds' arguments and returns. -/
def sArgs (curE zvE tbE : ℕ) : List E :=
  D.I.2.2.cap ++ [0, 0, D.cL curE * gen ^ (2 * 6) * gen * gen ^ (2 * 4), D.I.2.1,
    ptr zvE * gen ^ 39 * gen ^ D.τ, ptr tbE]
def sRets (curE : ℕ) : List E :=
  D.S.2.2.cap ++ [D.cL curE * gen ^ (2 * 6) * gen * gen ^ (2 * 4) * gen ^ (2 * 6), D.S.2.1]

/-- The rate cells layer `s` starts with: the committed word's for the first. -/
def cells (s : ℕ) : E × E := if s = 0 then Keccak.scalarCells D.committed dsObserve else (0, 0)

/-- The layers' buffers' bases, from the calls' frame pointers. -/
def lsOf (fs : String → ℕ) (ps : List ℕ) (k : ℕ) : ℕ := ps.getD (k + 1) 0 + fs (D.lname k)

/-- **Layer `s`'s call.** -/
def layKid (fs : String → ℕ) (B curE tbE stE : ℕ) (s : ℕ) : KidG where
  f := D.lname s
  taken := true
  args := fun _ ↦ (D.layer s).cap ++ [(D.cells s).1, (D.cells s).2, ptr (curE + D.lcur s),
    gen ^ (D.layer s).y, gen ^ ((D.layer s).y / 8), gen ^ ((D.layer s).y % 8),
    ptr (B + D.o201 + 22 * s), ptr (B + D.o201 + 22 * (s + 1)), keccakIota D.τ s (D.layer s).c,
    ptr tbE, ptr stE]
  Lin := fun ps ↦ layerLin (D.layer s) (firstOf s) (D.CL B (D.lsOf fs ps.dropLast) s) (curE + D.lcur s)
    (B + D.o201 + 22 * (s + 1)) tbE (ps.getLast?.getD 0 + fs (D.lname s))
  Out := fun ps rets Lout ↦ rets = (D.layer s).rets (firstOf s) (ptr (curE + D.lcur s)) ∧
    Lout = layerBufs (D.layer s) (firstOf s) (ptr (curE + D.lcur s))
      (ps.getLast?.getD 0 + fs (D.lname s))

/-- **The calls.** -/
def kids (fs : String → ℕ) (B curE chiE olE zvE slE tbE stE : ℕ) : List KidG :=
  [⟨name% «verify_keccak_loop0», true, fun _ ↦ [1, gen ^ (D.τ - 4), ptr B, ptr chiE * gen ^ 4],
      fun _ ↦ [(chiE, D.chis), (B, D.c0.point)], fun _ ↦ Returns []⟩] ++
  (List.range 12).map (D.layKid fs B curE tbE stE) ++
  [⟨plainName 0, true, fun _ ↦ D.oArgs curE zvE tbE, fun _ ↦ D.lin curE chiE olE zvE slE tbE,
      fun _ ↦ Returns (D.oRets curE)⟩,
    ⟨name% «verify_keccak_loop1», true, fun _ ↦ [1, gen ^ (D.τ - 4), ptr zvE * gen ^ 4, ptr B],
      fun _ ↦ [(zvE, D.op), (B, D.c0.point)], fun _ ↦ Returns []⟩,
    ⟨plainName 1, true, fun _ ↦ D.iArgs curE zvE tbE, fun _ ↦ D.lin curE chiE olE zvE slE tbE,
      fun _ ↦ Returns (D.iRets curE)⟩,
    ⟨plainName 0, true, fun _ ↦ D.sArgs curE zvE tbE, fun _ ↦ D.lin curE chiE olE zvE slE tbE,
      fun _ ↦ Returns (D.sRets curE)⟩,
    ⟨name% «verify_keccak_loop2», true, fun ps ↦ [1, gen ^ (D.τ - 4), ptr zvE * gen ^ 43,
        ptr (D.lsOf fs ps 11)],
      fun ps ↦ [(zvE + qkeccakVarsCap, D.point),
        (D.lsOf fs ps.dropLast 11, (D.layer 11).chs (firstOf 11))], fun _ ↦ Returns []⟩]

variable {D}

theorem inst_length (h : D.Ok) : D.inst.length = D.τ := by
  have := h.2.2.1; simp [inst]; omega

theorem inst_getD (h : D.Ok) {i : ℕ} (hi : i < D.τ) : D.inst.getD i 0 = D.chis.getD i 0 := by
  have := h.2.2.1
  simp [inst, List.getD_eq_getElem?_getD, hi]

theorem O1_length (h : D.Ok) : D.O.1.length = 6 := by
  rw [O, plainRun_length, h.2.2.2.2.2.2.1]

theorem I1_length (h : D.Ok) : D.I.1.length = 4 := by
  rw [I, plainRun_length, h.2.2.2.2.2.2.2.1]

theorem S1_length (h : D.Ok) : D.S.1.length = 6 := by
  rw [S, plainRun_length, h.2.2.2.2.2.2.2.2.1]

theorem L_point (h : D.Ok) : D.L.1.point.length = D.τ - 3 := by
  rw [L_eq h]; exact D.chain_point h le_rfl

theorem op_eq : D.op = (D.inst.take 4 ++ D.inst.drop 4) ++ D.O.1 := rfl

theorem op_length (h : D.Ok) : D.op.length = D.τ + 6 := by
  rw [op_eq, List.take_append_drop, List.length_append, inst_length h, O1_length h]

theorem point_length (h : D.Ok) : D.point.length = D.τ + 6 := by
  have := h.1
  simp only [point, List.length_append, I1_length h, List.length_take, L_point h, S1_length h]
  omega

theorem xs_length (h : D.Ok) : D.xs.length = D.lcur 12 + 97 := by
  obtain ⟨-, -, -, -, -, -, hmO, hmI, hmS, hsl, -, -⟩ := id h
  rw [xs_eq h]
  simp only [List.length_append, List.length_singleton, flatMap_pairs_length, hmO, hmI, hmS, hsl,
    flatMap_range_length _ (fun k hk ↦ ltXs_length h hk), lcur]

theorem c0_point_getD (h : D.Ok) {j : ℕ} (hj : j < D.τ - 4) :
    D.c0.point.getD j 0 = D.chis.getD (4 + j) 0 := by
  have hl := inst_length h
  simp only [c0, vkFirst]
  rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_eq_getElem?_getD, List.getElem?_drop,
    ← List.getD_eq_getElem?_getD, inst_getD h (by omega)]

theorem cL_eq (curE : ℕ) : D.cL curE = ptr curE * gen ^ D.lcur 12 := (ptr_mul_gen _ _).symm

end VkData

variable {fs : String → ℕ} {cert : String → V → ℕ}

/-- **A copy loop, complete**, copying `m` words between two entries of the caller's words. -/
theorem loop_complete {name : String} {fn : Fn} (hf : coreProgram.find? name = some fn)
    (hb : fn.body = copyLoopT name) (hpar : fn.params = [.n 0, .n 1, .n 2, .n 3])
    (hS : name ∈ vkKidS) (κ : ℕ) {L : Main.Layout} {m : ℕ} (hm1 : 0 < m) (hm2 : m < ordG)
    {db sb dj sj : ℕ} {dw sw : List E} (hd : (db, dw) ∈ L) (hs : (sb, sw) ∈ L)
    (hdl : dj + m ≤ dw.length) (hsl : sj + m ≤ sw.length)
    (heq : ∀ j < m, dw.getD (dj + j) 0 = sw.getD (sj + j) 0) {dst src : E}
    (hdst : dst = ptr db * gen ^ dj) (hsrc : src = ptr sb * gen ^ sj) :
    CompleteAtD fs cert κ name L [1, gen ^ m, dst, src] (Returns []) := by
  refine completeAtD_of_relIn vkKidS_pure hS fun rd _ hmem ↦ ?_
  have hD := memL_entry hmem hd
  have hS' := memL_entry hmem hs
  subst hdst hsrc
  refine (copyLoop_relIn hf hb hpar (m := m) (fun j hj ↦ ⟨dw.getD (dj + j) 0, ?_, ?_⟩)
    (fun j hj ↦ ⟨?_, ?_⟩)).2 (gen_pow_ne_one hm1 hm2)
  · rw [mul_assoc, ← pow_add, loadHolds_mul_gen_pow, heq j hj, add_zero]
    exact ClaimLay.getD_load hS' (by omega)
  · rw [mul_assoc, ← pow_add, loadHolds_mul_gen_pow, add_zero]
    exact ClaimLay.getD_load hD (by omega)
  · rw [mul_assoc, ← pow_add]; exact inR_entry hs (by omega)
  · rw [mul_assoc, ← pow_add]; exact inR_entry hd (by omega)

namespace VkData

variable {D : VkData}

theorem ptr_mul_gen1 (b : ℕ) : ptr b * gen = ptr (b + 1) := by
  rw [← ptr_mul_gen, pow_one]

theorem L1_point (h : D.Ok) : D.L.1.point = (D.layer 11).chs (firstOf 11) := by
  rw [L_eq h, D.layer_succ h (by norm_num : 11 < 12)]
  rfl

/-- The committed outputs' rounds, honestly. -/
theorem oMeaning (h : D.Ok) {rd : Reader} {curE chiE olE zvE slE tbE : ℕ}
    (hm : MemL rd (D.lin curE chiE olE zvE slE tbE)) :
    MeaningPlainRounds (plainCount 0) 0 rd (D.oArgs curE zvE tbE) (D.oRets curE) := by
  obtain ⟨-, -, hmO, -⟩ := xs_reads h (memL_entry hm (b := curE) (ws := D.xs) (by simp [lin]))
  have hop := memL_entry hm (b := zvE) (ws := D.op) (by simp [lin])
  obtain ⟨a, b, c, d, e, hc⟩ := five_of_length (L_ok h).2
  rw [oArgs, hc]
  simp only [List.cons_append, List.nil_append, MeaningPlainRounds]
  refine ⟨D.mO, h.2.2.2.2.2.2.1, by rw [cL]; exact hmO, fun w _ ↦ ?_⟩
  rw [← hc, O_run h w]
  refine ⟨?_, by simp [oRets, plainCount]⟩
  rw [op_eq] at hop
  have := (readsAt_append.1 hop).2
  rwa [List.take_append_drop, inst_length h] at this

/-- The inputs' rounds, honestly. -/
theorem iMeaning (h : D.Ok) {rd : Reader} {curE chiE olE zvE slE tbE : ℕ}
    (hm : MemL rd (D.lin curE chiE olE zvE slE tbE)) :
    MeaningPlainRounds (plainCount 1) 1 rd (D.iArgs curE zvE tbE) (D.iRets curE) := by
  obtain ⟨-, -, -, -, hmI, -⟩ := xs_reads h (memL_entry hm (b := curE) (ws := D.xs) (by simp [lin]))
  have hpt := memL_entry hm (b := zvE + qkeccakVarsCap) (ws := D.point) (by simp [lin])
  obtain ⟨a, b, c, d, e, hc⟩ := five_of_length (O_ok h).2
  rw [iArgs, hc]
  simp only [List.cons_append, List.nil_append, MeaningPlainRounds]
  refine ⟨D.mI, h.2.2.2.2.2.2.2.1, ?_, fun w hw ↦ ?_⟩
  · rw [cL, ptr_mul_gen, ptr_mul_gen1]; exact hmI
  have hw' : w = D.word := scalarCells_inj ((hw trivial).symm)
  subst hw'
  rw [← hc, I_run h]
  refine ⟨?_, by simp [iRets, plainCount]⟩
  rw [show ptr zvE * gen ^ 39 = ptr (zvE + qkeccakVarsCap) from ptr_mul_gen _ _]
  exact (readsAt_append.1 (readsAt_append.1 hpt).1).1

/-- The inputs' opening's rounds, honestly. -/
theorem sMeaning (h : D.Ok) {rd : Reader} {curE chiE olE zvE slE tbE : ℕ}
    (hm : MemL rd (D.lin curE chiE olE zvE slE tbE)) :
    MeaningPlainRounds (plainCount 0) 0 rd (D.sArgs curE zvE tbE) (D.sRets curE) := by
  obtain ⟨-, -, -, -, -, hmS, -⟩ := xs_reads h (memL_entry hm (b := curE) (ws := D.xs) (by simp [lin]))
  have hpt := memL_entry hm (b := zvE + qkeccakVarsCap) (ws := D.point) (by simp [lin])
  obtain ⟨a, b, c, d, e, hc⟩ := five_of_length (I_ok h).2
  rw [sArgs, hc]
  simp only [List.cons_append, List.nil_append, MeaningPlainRounds]
  refine ⟨D.mS, h.2.2.2.2.2.2.2.2.1, ?_, fun w _ ↦ ?_⟩
  · rw [cL, ptr_mul_gen, ptr_mul_gen1, ptr_mul_gen]; exact hmS
  rw [← hc, S_run h w]
  refine ⟨?_, by simp [sRets, plainCount]⟩
  have := (readsAt_append.1 hpt).2
  have hτ := h.1
  rw [List.length_append, I1_length h, List.length_take, L_point h,
    show min (D.τ - 4) (D.τ - 3) = D.τ - 4 by omega, ptr_mul_gen,
    show zvE + qkeccakVarsCap + (4 + (D.τ - 4)) = zvE + 39 + D.τ by simp; omega] at this
  rwa [ptr_mul_gen, ptr_mul_gen]

variable {fs : String → ℕ} {cert : String → V → ℕ}

end VkData

end
end LeanVM.Guest.B1.VerifySub
