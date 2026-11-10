/-
  LeanVM.Guest.B1.VerifySub.H.Runs

  An honest child's segments read back: the sponges carried, the out-of-domain sample, the bus's
  grind and challenges, the GKR's ends and the ring map's grind and challenges are `H/Kids`' honest
  values.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Kids
public import LeanVM.Guest.B1.Gkr.SpecInv
public import LeanVM.Guest.B1.VerifySub.Sizes
public import LeanVM.Guest.B1.Fs.Templates
public import LeanVM.Guest.B1.Gkr.WalkC
public import LeanVM.Guest.B1.Gkr.VbgComplete
public import LeanVM.Guest.B1.Bits.BusGrind
public import LeanVM.Guest.B1.Placement.Kappas

/-!
# The segments read back

`vi_grind`, `vi_sampleNG`: a grind's nonce and proof of work, and the samples after it, from the
carried run. On an honest child's segments `S`:

* `c1` .. `c7`, `cSR`: every segment starts from a carried sponge;
* `ood_inv`: the out-of-domain sample reads the grind's nonce `oodN` and the value `oodV`, its
  point is `oodZ` and the sponge after it `sZ` with the value absorbed;
* `bus_inv`: the bus reads its grind's nonce `busN`, on the permutation `busSt`, and squeezes the
  sixteen weights and `β` from it;
* `gkr_inv`: the GKR starts and ends with nothing waiting, its point of `d` coordinates, its three
  leaves;
* `ring_inv`: the ring map reads its grind's nonce `ringN`, on `ringSt`, and squeezes `rchs`; the
  target is `ringTarget` of them and the batching challenge's sponge `s7` the squeezes' end;
* the proofs of work as `grind_check` reads them (`oodPow`, `busPow`, `ringPow`), and the bus
  depth's range (`d_bounds`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Node

@[expose] public section

/-! ## Read-back -/

/-- **A grind of `bits ≠ 0`, read back**: the nonce, its proof of work, and the challenge it
grounds. -/
theorem vi_grind {bits : ℕ} (hb : bits ≠ 0) {s : Fs} {zs : List E} {os : List (List Opening)}
    {R : List (Digest × ℕ × ℕ)} {u : Unit} {st' : Tables.TSt}
    (h : Tables.runT (VerifierProgram.grindProofOfWork bits) ⟨s, none, zs, os, R⟩ =
      some (u, st')) :
    ∃ n zs', zs = n :: zs' ∧ s.GrindOk bits n ∧
      st' = ⟨⟨capOf (s.nonceState n), []⟩, some (challengeOf (s.nonceState n)), zs', os, R⟩ := by
  unfold VerifierProgram.grindProofOfWork at h
  simp only [hb, ↓reduceIte] at h
  cases zs with
  | nil => simp [Tables.runT] at h
  | cons n zs' =>
    simp only [Tables.runT] at h
    split at h
    · rename_i hp
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨n, zs', rfl, Or.inr hp, h.2.symm⟩
    · simp at h

/-- **`m + 1` samples after a grind**: the grounded challenge, then `m` squeezes. -/
theorem vi_sampleNG (m : ℕ) (s : Fs) (c : E) (zs : List E) (os : List (List Opening))
    (R : List (Digest × ℕ × ℕ)) :
    Tables.runT (VerifierProgram.sampleChallenges (m + 1)) ⟨s, some c, zs, os, R⟩ =
      some (c :: (s.squeezeN m).1, ⟨(s.squeezeN m).2, none, zs, os, R⟩) := by
  simp only [VerifierProgram.sampleChallenges, prog_bind_eq, Tables.runT_bind]
  rw [show Tables.runT VerifierProgram.sampleChallenge ⟨s, some c, zs, os, R⟩ =
    some (c, ⟨s, none, zs, os, R⟩) from rfl, Option.bind_some]
  rw [Tables.runT_sampleN m, Option.bind_some]
  rfl

theorem squeezeN_pend : ∀ (n : ℕ) (s : Fs), s.pend = [] → (s.squeezeN n).2.pend = []
  | 0, _, h => h
  | n + 1, s, _ => squeezeN_pend n s.squeeze.2 rfl

theorem squeezeN_length : ∀ (n : ℕ) (s : Fs), (s.squeezeN n).1.length = n
  | 0, _ => rfl
  | n + 1, s => by simp [Fs.squeezeN, squeezeN_length n]

theorem fs_eta {s : Fs} (h : s.pend = []) : s = ⟨s.cap, []⟩ := by
  cases s; simp only at h; simp [h]

/-- The seed's sponge is carried. -/
theorem seedFs_carries (seed pi : Digest) : ∃ sp, (seedFs seed pi).Carries sp :=
  ⟨⟨keccakF1600 (seedInput seed pi), [], none⟩, rfl, rfl, rfl⟩

/-- The push side's total of the memory's log `m` and the heights `hs`. -/
def pushTot (m : ℕ) (hs : List ℕ) : ℕ := ((List.range 54).map fun b ↦ 2 ^ pushKappa m hs b).sum

theorem heights_length6 (rowsN : List ℕ) (h : rowsN.length = 6) :
    (Tables.tableHeightsOf rowsN).length = 6 := by
  simp [Tables.tableHeightsOf, h, tableLogFloors]

theorem colKappa_list : (List.range Tables.nCommittedCols).map
    (fun c ↦ (Tables.colKappaSrc c, Tables.colKappaAdj c)) =
    List.replicate 3 (1, 0) ++ [(0, 19), (7, 6)] ++ List.replicate 13 (2, 0) ++
      List.replicate 13 (3, 0) ++ List.replicate 7 (4, 0) ++ List.replicate 14 (5, 0) ++
      List.replicate 14 (6, 0) ++ List.replicate 28 (7, 0) := by decide

/-- **The stack's total**, column by column. -/
theorem stackTotal_eq (lm h0 h1 h2 h3 h4 h5 : ℕ) :
    Tables.stackTotal (columnKappas lm 19 [h0, h1, h2, h3, h4, h5]) =
      3 * 2 ^ lm + 2 ^ 19 + 64 * 2 ^ h5 + 13 * 2 ^ h0 + 13 * 2 ^ h1 + 7 * 2 ^ h2 +
        14 * 2 ^ h3 + 14 * 2 ^ h4 + 28 * 2 ^ h5 := by
  unfold Tables.stackTotal
  rw [Tables.committedKappas_columnKappas lm _ rfl]
  have e : (List.range Tables.nCommittedCols).map (fun c ↦
      ([0, lm, h0, h1, h2, h3, h4, h5].getD (Tables.colKappaSrc c) 0 + Tables.colKappaAdj c)) =
      ((List.range Tables.nCommittedCols).map
        (fun c ↦ (Tables.colKappaSrc c, Tables.colKappaAdj c))).map
        (fun p ↦ [0, lm, h0, h1, h2, h3, h4, h5].getD p.1 0 + p.2) := by
    rw [List.map_map]; rfl
  rw [e, colKappa_list]
  simp only [List.map_append, List.map_replicate, List.sum_append, List.sum_replicate,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.getD_cons_succ,
    List.getD_cons_zero, smul_eq_mul, Nat.add_zero, pow_add]
  ring

/-- **The push side's total**, block by block. -/
theorem pushTot_eq (lm h0 h1 h2 h3 h4 h5 : ℕ) :
    pushTot lm [h0, h1, h2, h3, h4, h5] =
      1 + 2 ^ lm + 2 ^ 19 + 5 * 2 ^ h0 + 5 * 2 ^ h1 + 3 * 2 ^ h2 + 5 * 2 ^ h3 + 5 * 2 ^ h4 +
        28 * 2 ^ h5 := by
  unfold pushTot
  rw [show (List.range 54).map (fun b ↦ 2 ^ pushKappa lm [h0, h1, h2, h3, h4, h5] b) =
    ((List.range 54).map (pushKappa lm [h0, h1, h2, h3, h4, h5])).map (2 ^ ·) from
    (List.map_map ..).symm, pushKappas_eq]
  simp only [List.map_append, List.map_replicate, List.sum_append, List.sum_replicate,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, smul_eq_mul]
  ring

/-- **The push side fits the stack**: its total is at most the stack's plus one. -/
theorem pushTot_le_stack (lm : ℕ) {hs : List ℕ} (hl : hs.length = 6) :
    pushTot lm hs ≤ Tables.stackTotal (columnKappas lm 19 hs) + 1 := by
  match hs, hl with
  | [h0, h1, h2, h3, h4, h5], _ =>
    rw [pushTot_eq, stackTotal_eq]
    omega

theorem pushTot_ge (lm : ℕ) {hs : List ℕ} (hl : hs.length = 6) :
    2 ^ lm + 2 ^ 19 + 1 ≤ pushTot lm hs := by
  match hs, hl with
  | [h0, h1, h2, h3, h4, h5], _ =>
    rw [pushTot_eq]
    omega

namespace ChildSegs

variable {bytecode : List K} {seed : Digest} {c : Child} (S : ChildSegs bytecode seed c)

/-! ## The carried sponges -/

theorem c1 : ∃ sp, S.s1.Carries sp := Tables.RunsTo.carries S.runS (seedFs_carries _ _)

theorem cSR : ∃ sp, S.sR.Carries sp := by
  obtain ⟨sp, h⟩ := S.c1
  exact ⟨_, carries_absorb (carries_absorb h _ _) _ _⟩

theorem c2 : ∃ sp, S.s2.Carries sp := Tables.RunsTo.carries S.runO S.cSR
theorem c3 : ∃ sp, S.s3.Carries sp := Tables.RunsTo.carries S.runB S.c2
theorem c4 : ∃ sp, S.s4.Carries sp := Tables.RunsTo.carries S.runG S.c3
theorem c5 : ∃ sp, S.s5.Carries sp := Tables.RunsTo.carries S.runT S.c4
theorem c6 : ∃ sp, S.s6.Carries sp := Tables.RunsTo.carries S.runK S.c5
theorem c7 : ∃ sp, S.s7.Carries sp := Tables.RunsTo.carries S.runR S.c6

/-! ## The bus depth -/

theorem d_eq (hbl : bytecode.length = 2 ^ 23) : S.d = log2Ceil S.pushT := by
  show busDepth S.layout = _
  rw [S.hlayout]
  exact pushDepth_eq hbl _ _ S.hrowsL

/-- **The bus depth**: at least `20`, at most `29`: the push side's total is at most the
stack's plus one. -/
theorem d_bounds (hbl : bytecode.length = 2 ^ 23) : 20 ≤ S.d ∧ S.d ≤ 29 := by
  rw [S.d_eq hbl]
  have hh := heights_length6 S.rowsN S.hrowsL
  have hpT : S.pushT = pushTot S.logMem (Tables.tableHeightsOf S.rowsN) := rfl
  refine ⟨lt_log2Ceil_iff.2 (by
    have := pushTot_ge S.logMem hh
    have := Nat.one_le_two_pow (n := S.logMem)
    omega), ?_⟩
  have h28 := S.hmu28
  rw [S.hlayout, stackLog_eq hbl] at h28
  have hst : Tables.stackTotal (columnKappas S.logMem 19 (Tables.tableHeightsOf S.rowsN)) ≤
      2 ^ 28 := log2Ceil_le_iff.mp (by omega)
  have hp := pushTot_le_stack S.logMem hh
  exact log2Ceil_le_iff.mpr (by
    calc S.pushT ≤ 2 ^ 28 + 1 := by
          rw [hpT]; omega
      _ ≤ 2 ^ 29 := by norm_num)

/-! ## The out-of-domain sample -/

/-- **The out-of-domain sample, read back.** -/
theorem ood_inv : S.xsO = [S.oodN, S.oodV] ∧ S.sR.GrindOk Whir.oodGrindingBits S.oodN ∧
    S.ood = (fun x ↦ eqEval S.oodZ x, S.oodV) ∧ S.s2 = S.sZ.absorb S.oodV dsObserve := by
  obtain ⟨sp, hsp⟩ := S.cSR
  have h := Tables.RunsTo.toT S.runO hsp []
  rw [List.append_nil] at h
  obtain ⟨m, hm⟩ : ∃ m, S.layout.stackLog = m + 1 :=
    ⟨S.layout.stackLog - 1, by have := S.hmu22; omega⟩
  have hμ : S.μs - 1 = m := by show S.layout.stackLog - 1 = m; omega
  generalize hp : readOod S.layout.stackLog = p at h
  rw [hm] at hp
  subst hp
  unfold readOod at h
  obtain ⟨u, st1, h1, h2⟩ := Tables.runT_bind_some h
  obtain ⟨n, zs, hxs, hok, rfl⟩ := vi_grind (by decide) h1
  obtain ⟨z, st2, h3, h4⟩ := Tables.runT_bind_some h2
  rw [vi_sampleNG] at h3
  simp only [Option.some.injEq, Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  obtain ⟨v, st3, h5, h6⟩ := Tables.runT_bind_some h4
  obtain ⟨zs', rfl, rfl⟩ := Tables.runT_readE_some h5
  obtain ⟨e1, e2⟩ := Tables.runT_pure_some h6
  simp only [Tables.TSt.mk.injEq] at e2
  obtain ⟨e3, -, rfl, -, -⟩ := e2
  have hN : S.oodN = n := by show S.xsO.getD 0 0 = n; rw [hxs]; rfl
  have hV : S.oodV = v := by show S.xsO.getD 1 0 = v; rw [hxs]; rfl
  have hZ : S.oodZ = challengeOf (S.sR.nonceState n) ::
      ((⟨capOf (S.sR.nonceState n), []⟩ : Fs).squeezeN m).1 := by
    show challengeOf S.oodSt :: ((⟨capOf S.oodSt, []⟩ : Fs).squeezeN (S.μs - 1)).1 = _
    rw [hμ, show S.oodSt = S.sR.nonceState n by show S.sR.nonceState S.oodN = _; rw [hN]]
  have hZs : S.sZ = ((⟨capOf (S.sR.nonceState n), []⟩ : Fs).squeezeN m).2 := by
    show ((⟨capOf S.oodSt, []⟩ : Fs).squeezeN (S.μs - 1)).2 = _
    rw [hμ, show S.oodSt = S.sR.nonceState n by show S.sR.nonceState S.oodN = _; rw [hN]]
  refine ⟨by rw [hxs, hN, hV], by rw [hN]; exact hok, by rw [hZ, hV]; exact e1, by rw [hZs, hV]; exact e3⟩

theorem sZ_pend : S.sZ.pend = [] := squeezeN_pend _ _ rfl

/-- The out-of-domain grind's proof of work, as `grind_check__L15` reads it. -/
theorem oodPow : ((cellsOfState S.oodSt false 1).limb 0).lane.toNat % 2 ^ 15 = 0 :=
  (grindOk_iff (s := S.sR) (bits := Whir.oodGrindingBits) (by decide) S.oodN).1 S.ood_inv.2.1

theorem oodZ_length : S.oodZ.length = S.μs := by
  show (challengeOf S.oodSt :: ((⟨capOf S.oodSt, []⟩ : Fs).squeezeN (S.μs - 1)).1).length = _
  rw [List.length_cons, squeezeN_length]
  have := S.hmu22
  show S.layout.stackLog - 1 + 1 = S.layout.stackLog
  omega

/-! ## The bus's challenges -/

/-- The bus's grind's permutation is the nonce's on the sponge after the value. -/
theorem busSt_eq : S.busSt = S.s2.nonceState S.busN := by
  show omState S.sZ.cap [S.oodV] (some S.busN) = _
  rw [S.ood_inv.2.2.2, omState]
  conv_rhs => rw [fs_eta S.sZ_pend]
  rfl

/-- **The bus's challenges, read back.** -/
theorem bus_inv (hbl : bytecode.length = 2 ^ 23) : S.xsB = [S.busN] ∧
    S.s2.GrindOk (busGrindingBits S.d) S.busN ∧
    S.wb = (challengeOf S.busSt :: ((⟨capOf S.busSt, []⟩ : Fs).squeezeN 15).1,
      ((⟨capOf S.busSt, []⟩ : Fs).squeezeN 15).2.squeeze.1) ∧
    S.s3 = ((⟨capOf S.busSt, []⟩ : Fs).squeezeN 15).2.squeeze.2 := by
  have hd := S.d_bounds hbl
  obtain ⟨sp, hsp⟩ := S.c2
  have h := Tables.RunsTo.toT S.runB hsp []
  rw [List.append_nil] at h
  generalize hp : busChallenges (busDepth S.layout) = p at h
  unfold busChallenges at hp
  subst hp
  obtain ⟨u, st1, h1, h2⟩ := Tables.runT_bind_some h
  have hb0 : busGrindingBits (busDepth S.layout) ≠ 0 := by
    rw [busGrindingBits_of (show 4 ≤ busDepth S.layout from by
      show 4 ≤ S.d; omega)]
    show S.d - 3 ≠ 0; omega
  obtain ⟨n, zs, hxs, hok, rfl⟩ := vi_grind hb0 h1
  obtain ⟨w, st2, h3, h4⟩ := Tables.runT_bind_some h2
  rw [show (2 : ℕ) ^ busBits = 15 + 1 from rfl, vi_sampleNG] at h3
  simp only [Option.some.injEq, Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  obtain ⟨b, st3, h5, h6⟩ := Tables.runT_bind_some h4
  rw [Tables.runT_sampleE] at h5
  simp only [Option.some.injEq, Prod.mk.injEq] at h5
  obtain ⟨rfl, rfl⟩ := h5
  obtain ⟨e1, e2⟩ := Tables.runT_pure_some h6
  simp only [Tables.TSt.mk.injEq] at e2
  obtain ⟨e3, -, rfl, -, -⟩ := e2
  have hN : S.busN = n := by show S.xsB.getD 0 0 = n; rw [hxs]; rfl
  have hS : S.busSt = S.s2.nonceState n := by rw [S.busSt_eq, hN]
  refine ⟨by rw [hxs, hN], by rw [hN]; exact hok, by rw [hS]; exact e1, by rw [hS]; exact e3⟩

/-- The bus grind's proof of work, as `bus_grind_check__L{d - 16}` reads it. -/
theorem busPow (hbl : bytecode.length = 2 ^ 23) :
    ((cellsOfState S.busSt false 1).limb 0).lane.toNat % 2 ^ busGrindBits (S.d - 16) = 0 := by
  have hd := S.d_bounds hbl
  have e : busGrindBits (S.d - 16) = busGrindingBits S.d := by
    unfold busGrindBits; congr 1; show 16 + (S.d - 16) = S.d; omega
  have hb0 : busGrindingBits S.d ≠ 0 := by rw [busGrindingBits_of (by omega)]; omega
  rw [e, S.busSt_eq]
  exact (grindOk_iff hb0 S.busN).1 (S.bus_inv hbl).2.1

theorem s3_pend (hbl : bytecode.length = 2 ^ 23) : S.s3.pend = [] := by
  rw [(S.bus_inv hbl).2.2.2]; rfl

theorem wb_length (hbl : bytecode.length = 2 ^ 23) : S.wb.1.length = 16 := by
  rw [(S.bus_inv hbl).2.2.1]
  simp [squeezeN_length]

/-! ## The GKR -/

/-- **The GKR, read back**: it starts and ends with nothing waiting, on five capacity cells; its
point has `d` coordinates and it has three leaves. -/
theorem gkr_inv (hbl : bytecode.length = 2 ^ 23) : S.s3 = ⟨S.s3.cap, []⟩ ∧
    S.s4 = ⟨S.s4.cap, []⟩ ∧ S.s4.cap.length = 5 ∧ S.s3.cap.length = 5 ∧
    S.rG.2.1.length = S.d ∧ S.rG.2.2.length = 3 := by
  have hd := S.d_bounds hbl
  have h3 : S.s3 = ⟨S.s3.cap, []⟩ := fs_eta (S.s3_pend hbl)
  have hc3 : S.s3.cap.length = 5 := by
    rw [(S.bus_inv hbl).2.2.2]; simp [Fs.squeeze, capOf]
  have hrun : RunsTo (Tables.gkrPhase S.d) ⟨S.s3.cap, []⟩ S.xsG S.rG S.s4 := by
    rw [← h3]; exact S.runG
  have hc : ∃ sp, (⟨S.s3.cap, []⟩ : Fs).Carries sp := by rw [← h3]; exact S.c3
  obtain ⟨-, -, -, -, -, hsF, hr, hpl⟩ := Tables.gk_walk hrun hc
  obtain ⟨hcl, hvl, hpe⟩ := Tables.gkSl_inv (xs := S.xsG) (sh := S.d % 2) hc3 (S.d / 2)
  refine ⟨h3, fs_eta (by rw [hsF]; exact hpe (Or.inr (by omega))), by rw [hsF]; exact hcl, hc3,
    by rw [hr]; exact hpl, by rw [hr]; exact hvl⟩

/-! ## The ring map -/

/-- **The ring map, read back.** -/
theorem ring_inv : S.xsR = [S.ringN] ∧ S.s6.GrindOk Whir.batchGrindingBits S.ringN ∧
    S.rs.1 = ringTarget S.kc.2.2 (S.rchs.take ringMapWidth) (S.rchs.drop ringMapWidth) ∧
    S.s7 = ((⟨capOf S.ringSt, []⟩ : Fs).squeezeN 15).2 := by
  obtain ⟨sp, hsp⟩ := S.c6
  have h := Tables.RunsTo.toT S.runR hsp []
  rw [List.append_nil] at h
  generalize hp : ringSwitch S.kc.2.1 S.kc.2.2 = p at h
  unfold ringSwitch at hp
  subst hp
  obtain ⟨u, st1, h1, h2⟩ := Tables.runT_bind_some h
  obtain ⟨n, zs, hxs, hok, rfl⟩ := vi_grind (by decide) h1
  obtain ⟨w, st2, h3, h4⟩ := Tables.runT_bind_some h2
  rw [show 2 * ringMapWidth = 15 + 1 from rfl, vi_sampleNG] at h3
  simp only [Option.some.injEq, Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  obtain ⟨e1, e2⟩ := Tables.runT_pure_some h4
  simp only [Tables.TSt.mk.injEq] at e2
  obtain ⟨e3, -, rfl, -, -⟩ := e2
  have hN : S.ringN = n := by show S.xsR.getD 0 0 = n; rw [hxs]; rfl
  have hS : S.ringSt = S.s6.nonceState n := by show S.s6.nonceState S.ringN = _; rw [hN]
  have hC : S.rchs = challengeOf (S.s6.nonceState n) ::
      ((⟨capOf (S.s6.nonceState n), []⟩ : Fs).squeezeN 15).1 := by
    show challengeOf S.ringSt :: ((⟨capOf S.ringSt, []⟩ : Fs).squeezeN 15).1 = _
    rw [hS]
  refine ⟨by rw [hxs, hN], by rw [hN]; exact hok, by rw [e1, hC], by rw [hS]; exact e3⟩

/-- The ring map's grind's proof of work, as `grind_check__L14` reads it. -/
theorem ringPow : ((cellsOfState S.ringSt false 1).limb 0).lane.toNat % 2 ^ 14 = 0 :=
  (grindOk_iff (s := S.s6) (bits := Whir.batchGrindingBits) (by decide) S.ringN).1 S.ring_inv.2.1

theorem rchs_length : S.rchs.length = 16 := by
  show (challengeOf S.ringSt :: ((⟨capOf S.ringSt, []⟩ : Fs).squeezeN 15).1).length = 16
  simp [squeezeN_length]

end ChildSegs

end
end LeanVM.Guest.B1.VerifySub
