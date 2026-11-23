/-
  LeanVM.Guest.CoreMode.Fn.gkr_layer.Sound

  `gkr_layer`'s own routing facts and families, sound (`CoreMode/FnReg.lean`): its exponent facts, its loop's cursor, its family.
-/

module

public import LeanVM.Guest.EndExecCoreRes
public import LeanVM.Guest.EndExecCoreSt
public import LeanVM.Guest.CoreMode.Fn.verify_bus_gkr.ResGkrQ
public import LeanVM.Guest.CoreMode.Fn.verify_bus_gkr.ResGkrL
public import LeanVM.Guest.CoreMode.Fn.gkr_layer.Data
public import LeanVM.Guest.CoreMode.Fn.gkr_layer.Fam
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«gkr_layer__L»
import LeanVM.Guest.Data.ValNames.«gkr_layer__L_loop0»
import LeanVM.Guest.Data.ValNames.«gkr_layer__L0_L0»

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.CoreMode (CFun CRes CIdx ResF LtF rep_of capE resFam idxC baseC vw csSub)

public section

/-- **`gkr_layer`'s family holds** at an honest instance (`glQC`): `GlQ` puts its slot's cursor `q` words into its
stream with room for the layer's `4L + 12`; the head rounds read past the slot's cursor (value `s4#0`), the tail past
`8p + 32m` words on (`B1.Tables.gl_curs`). -/
theorem glQC_inst {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {f : String} {σ : Val} {bufs : List ℕ} {kids : List Tree} (ht : I.t = .node f σ bufs kids) {fn : Fn}
    (hf : coreProgram.find? f = some fn) : ∀ x : CRes, CoreMode.glQC fn x = true → x.Holds σ
  | .under gs r', h => fun _ ↦ glQC_inst hr hI ht hf r' h
  | .sub c q, h => by
    simp only [CoreMode.glQC, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hcs, rfl⟩ := h
    cases hl : List.lookup fn.name CoreMode.glCurs with
    | none => rw [hl] at hcs; simp at hcs
    | some cs =>
    rw [hl] at hcs
    simp only [Option.any_some] at hcs
    -- the layer
    obtain ⟨p, hp, o, ho, hn, rfl⟩ : ∃ p < 4, ∃ o < 2, fn.name = B1.Tables.glName p o ∧
        cs = (if p = 0 then [] else [(valf% «gkr_layer» "s4#0", 8 * p)]) ++ [(val% «gkr_layer__L0_L0» "tcur" + B1.Tables.glD p, 20 - 4 * o)] := by
      have hm := CoreMode.lookup_memL hl
      simp only [CoreMode.glCurs, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hm
      rcases hm with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩
      exacts [⟨0, by omega, 0, by omega, h1, rfl⟩, ⟨1, by omega, 0, by omega, h1, rfl⟩,
        ⟨2, by omega, 0, by omega, h1, rfl⟩, ⟨3, by omega, 0, by omega, h1, rfl⟩,
        ⟨0, by omega, 1, by omega, h1, rfl⟩, ⟨1, by omega, 1, by omega, h1, rfl⟩,
        ⟨2, by omega, 1, by omega, h1, rfl⟩, ⟨3, by omega, 1, by omega, h1, rfl⟩]
    have hf' : f = B1.Tables.glName p o := by rw [← find_name' hf, hn]
    subst hf'
    obtain ⟨fn', hfn', -, hb'⟩ := B1.Tables.glIs_sound (B1.Tables.glIs_layers p hp o ho)
    obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hfn')
    obtain ⟨m, q, h3, hm, h4, h5, hsl, hroom⟩ := glQ_all hr I hI p hp o ho σ bufs kids ht
    obtain ⟨args, rets, hv⟩ := inst_valid' hr hI ht
    obtain ⟨-, hb⟩ := Res.holds_of_valid Res.fs_pos hv hf
    rw [hb'] at hb
    obtain ⟨e21, -, -, -, e77, -⟩ :=
      B1.Tables.gl_curs (fun _ _ _ h ↦ Res.KidRel.rel h) hp ho hb h3 h4 h5 (by omega) hsl
    have hcap : (8192 : ℕ) < CoreMode.capE := by rw [CoreMode.capE_eq]; norm_num
    obtain ⟨cb, co⟩ := c
    have key : ∀ (v k : ℕ), σ (.n v) = σ (.n (valf% «gkr_layer» "stream")) * Protocol.Verifier.gen ^ q * Protocol.Verifier.gen ^ k →
        q + k + co < 8192 → cb = [(v, 1)] → (CRes.sub ⟨cb, co⟩ ⟨⟨[(valf% «gkr_layer» "stream", 1)], 0⟩, 1, .num 0, .num 8192⟩).Holds σ := by
      intro v k hvk hk hcb
      subst hcb
      refine ⟨0, 8192, q + k + co, CoreMode.rep_const (by rw [CoreMode.capE_eq]; norm_num),
        CoreMode.rep_const hcap, Nat.zero_le _, by omega, ?_⟩
      simp only [CoreMode.CCell.addrW, CoreMode.CCell.valW, CoreMode.prodW, vw, pow_one, mul_one, one_mul, hvk,
        ← Value.gen_pow_eq_ofK, addressOfIndex]
      simp only [mul_assoc, ← pow_add]
      ring_nf
    dsimp only at hcs
    split at hcs
    · rename_i x
      obtain ⟨e, he, hex⟩ := List.any_eq_true.mp hcs
      simp only [Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at hex
      obtain ⟨rfl, hco⟩ := hex
      simp only [List.mem_append, List.mem_singleton] at he
      rcases he with he | rfl
      · split at he
        · simp at he
        · simp only [List.mem_singleton] at he
          subst he
          have hco' : co < 8 * p := hco
          exact key (valf% «gkr_layer» "s4#0") 0 (by rw [e21, pow_zero, mul_one]) (by omega) rfl
      · have hco' : co < 20 - 4 * o := hco
        exact key (val% «gkr_layer__L0_L0» "tcur" + B1.Tables.glD p) (8 * p + 32 * m) e77 (by omega) rfl
    · cases hcs
  | .lt _ _, h | .nz _, h | .subR _ _, h | .subP _ _, h => by simp [CoreMode.glQC] at h

end

end LeanVM.Guest.EndExec

namespace LeanVM.Guest.EndExec

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory
open LeanVM.Guest.CoreMode (CFun CRes stK stSub GlF setG setG_eq ownG ownG_setG prodW vw capE rep_of
  rep_const idxC baseC valW_baseC)
open LeanVM.Guest.Value (gen_pow_eq_ofK gen_pow_inj)
open LeanVM.Guest.B1 (loadHolds_unique)
open LeanVM.Guest.Res (topAtoms)
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Prover.Exec

public section

/-- **A gkr layer's loop's cursor** in the stream: `GlLQ` and the iteration's load. -/
theorem st_gl {r : Ref} (hr : r.Ok) {I : Inst} (hI : I ∈ honestInsts coreProgram B2C.fs B2C.H r.hdr r.T)
    {p o : ℕ} (hp : p < 4) (ho : o < 2) {σ : Val} {bufs : List ℕ} {kids : List Tree}
    (ht : I.t = .node (B1.Tables.glLoopName p o) σ bufs kids) :
    ∃ a q, I.hdr.2 = ofK (addressOfIndex a) ∧ a + (2 + valf% «gkr_layer» "stream") < maxCells ∧
      σ (.n (valf% «gkr_layer» «_loop0» "cur")) = refMem r.img (a + (2 + valf% «gkr_layer» "stream")) * gen ^ q ∧ q + 32 ≤ 8192 := by
  obtain ⟨a, k, m, q, hhd, ha10, -, -, hkm, -, hld, hroom⟩ := glLQ_all hr I hI p hp o ho σ bufs kids ht
  obtain ⟨args, rets, fn', hf', -, es0, vs, hw, -, hh, -⟩ := inst_valid' hr hI ht
  obtain ⟨fn, hf, -, hb⟩ := B1.Tables.glIs_sound (B1.Tables.glIs_loops p hp o ho)
  obtain rfl : fn' = fn := Option.some.inj (hf'.symm.trans hf)
  exact ⟨a, q, hhd, ha10, (gll_next hp ho hb hw hh hld).1, room_of hkm hroom⟩

end

end LeanVM.Guest.EndExec

namespace LeanVM.Guest.CoreMode.Own.gkr_layer

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.EndExec
open LeanVM.Protocol.Verifier (gen)

public section

/-- **Its `x_m`, below `4`** (`GlQ`). -/
theorem expFacts_ok : ∀ c ∈ expFacts, ExpOk c := by
  intro c hc r hr J hJ σ bufs kids hJt fn hf v hv
  obtain ⟨p, hp, o, ho, rfl⟩ : ∃ p < 4, ∃ o < 2, c = (B1.Tables.glName p o, 3, none, 4) := by
    simp only [expFacts, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hc
    obtain ⟨n, hn, rfl⟩ := hc
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [⟨0, by omega, 0, by omega, rfl⟩, ⟨0, by omega, 1, by omega, rfl⟩, ⟨1, by omega, 0, by omega, rfl⟩,
      ⟨1, by omega, 1, by omega, rfl⟩, ⟨2, by omega, 0, by omega, rfl⟩, ⟨2, by omega, 1, by omega, rfl⟩,
      ⟨3, by omega, 0, by omega, rfl⟩, ⟨3, by omega, 1, by omega, rfl⟩]
  dsimp only at hJt hf hv ⊢
  obtain ⟨fn', hf', hp', -⟩ := B1.Tables.glIs_sound (B1.Tables.glIs_layers p hp o ho)
  obtain rfl : fn = fn' := Option.some.inj (hf.symm.trans hf')
  rw [hp', glParams_eq] at hv
  obtain rfl : V.n (valf% «gkr_layer» "x_m") = v := Option.some.inj hv
  obtain ⟨m, q, h3, hm, -⟩ := glQ_all hr J hJ p hp o ho σ bufs kids hJt
  exact ⟨m, hm, h3⟩

/-- **Its loop's cursor** (`st_gl`). -/
theorem stLoops_ok : ∀ c ∈ stLoops, StLoopOk c := by
  intro c hc
  obtain ⟨p, hp, o, ho, rfl⟩ : ∃ p < 4, ∃ o < 2, c = (B1.Tables.glLoopName p o, 2 + valf% «gkr_layer» "stream", valf% «gkr_layer» «_loop0» "cur", 32) := by
    simp only [stLoops, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at hc
    obtain ⟨n, hn, rfl⟩ := hc
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [⟨0, by omega, 0, by omega, rfl⟩, ⟨1, by omega, 0, by omega, rfl⟩, ⟨2, by omega, 0, by omega, rfl⟩,
      ⟨3, by omega, 0, by omega, rfl⟩, ⟨0, by omega, 1, by omega, rfl⟩, ⟨1, by omega, 1, by omega, rfl⟩,
      ⟨2, by omega, 1, by omega, rfl⟩, ⟨3, by omega, 1, by omega, rfl⟩]
  exact ⟨show 2 + valf% «gkr_layer» "stream" ≠ 0 by decide, show valf% «gkr_layer» «_loop0» "cur" < CoreMode.GB by unfold CoreMode.GB; decide,
    fun hr I hI σ bufs kids ht _ _ ↦ st_gl hr hI hp ho ht⟩

/-- **Its family.** -/
theorem fams_ok : ∀ c ∈ fams, OwnOk c := by
  intro c hc
  simp only [fams, List.mem_map] at hc
  obtain ⟨n, -, rfl⟩ := hc
  exact fun hr I hI σ bufs kids ht fn hf x h ↦ glQC_inst hr hI ht hf x h

end

end LeanVM.Guest.CoreMode.Own.gkr_layer
