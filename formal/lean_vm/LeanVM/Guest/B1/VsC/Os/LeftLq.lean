/-
  LeanVM.Guest.B1.VsC.Os.LeftLq

  A level's honest `level_queries` call on the run's openings: its cap honest and its static facts.
-/

module

public import LeanVM.Guest.B1.VsC.Os.LeftOs
public import LeanVM.Guest.B1.VsC.Oq.LqCap

/-!
# A level's `level_queries` call on the run's openings

`osCapDepth_eq`: every arm's levels' cap depths are the prover's (`Hints.capDepthOf`), one kernel
decision. `HonRun.lqCapOk_os`: level `l`'s phase of the run has an honest cap at the level's root
(`lqCapHonest`, its hypotheses from `openPhase`'s acceptance and `HonRun.agree`), the root the one
whose halves `level_roots` holds. `HonRun.lqStatic_os`: the honest `lqCall` of that phase, with the
honest data's rounds and final coefficients, has its static facts (`LqCall.Static`), and pops the
level's Merkle hints (`HonRun.lqPops_os`, at the prover's cap depth, `HonRun.capDepthOf_os`).
`HonRun.lqAt_os`: the level's `level_queries` (in `lqTable`, `HonRun.lqOk_os`) completes placed on that
call (`lqAG_all`), its pops the level's hints stream by stream, its batch the honest one
(`HonRun.lqMret_os`, by `oqChain_congr`).
-/

namespace LeanVM.Guest.B1.Whir

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest LeanVM.Guest.B1 LeanVM.Guest.B1.VsC
open LeanVM.Guest.Memory LeanVM.Guest.Complete
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

theorem zip_map_self {α β : Type _} (f : α → β) : ∀ l : List α, (l.map f).zip l = l.map fun a => (f a, a)
  | [] => rfl
  | a :: l => by rw [List.map_cons, List.zip_cons_cons, zip_map_self f l, List.map_cons]

/-- **The chain depends on the queries' values only below its count**, an odd query only at level `0`. -/
theorem oqChain_congr {odd base : ℕ} {mu : E} {ds ds' : ℕ → E} (hodd : odd = 1 → base = 1) :
    ∀ N, (∀ k < oqCount odd base N, ds k = ds' k) → oqChain odd base mu ds N = oqChain odd base mu ds' N
  | 0, h => by
    simp only [oqChain]
    by_cases h1 : odd = 1
    · simp only [h1, ↓reduceIte]
      rw [h 0 (by simp [oqCount, hodd h1, h1])]
    · simp only [h1, ↓reduceIte]
  | N + 1, h => by
    have ih := oqChain_congr (mu := mu) hodd N fun k hk => h k (by unfold oqCount at hk ⊢; split_ifs at hk ⊢ <;> omega)
    simp only [oqChain]
    rw [ih]
    by_cases hb : base = 1
    · simp only [hb, ↓reduceIte]
      rw [h (odd + 2 * N) (by simp only [oqCount, hb, ↓reduceIte]; omega),
        h (odd + 2 * N + 1) (by simp only [oqCount, hb, ↓reduceIte]; omega)]
    · simp only [hb, ↓reduceIte]
      rw [h N (by simp only [oqCount, hb, ↓reduceIte]; omega)]

/-- A `level_queries` call's batch, unfolded. -/
theorem lq_mret_eq (L : LqCall) (s : Oq) (q b cd : ℕ) (li : E) :
    (L.oqG s q b cd 0 li).mret = if s.final = 1 then 0 else
      oqChain (lqOdd q b) s.base li (fun k => qwFold s.base L.rounds (L.ws k)) (lqIters q b) := rfl

/-- An arm's levels' cap depths are the prover's. -/
def OsCapDepthOk (m : ℕ) : Bool :=
  (List.range 4).all fun ri => (osCfgR m ri).levels.all fun lv => lv.capDepth == Hints.capDepthOf lv.queries lv.depth

set_option maxRecDepth 100000 in
theorem osCapDepthOk_all : (List.range 15).all OsCapDepthOk = true := by decide +kernel

/-- **Every arm's levels' cap depths are the prover's** (`Hints.capDepthOf`). -/
theorem osCapDepth_eq {m ri l : ℕ} (hm : m < 15) (hri : ri < 4) (hl : l < (osCfgR m ri).levels.length) :
    (osLvA (osCfgR m ri) l).capDepth = Hints.capDepthOf (osLvA (osCfgR m ri) l).queries (osLvA (osCfgR m ri) l).depth := by
  have h := List.all_eq_true.mp osCapDepthOk_all m (List.mem_range.mpr hm)
  simp only [OsCapDepthOk, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have hmem : (osCfgR m ri).levels.getD l default ∈ (osCfgR m ri).levels := by
    rw [List.getD_eq_getElem _ _ hl]; exact List.getElem_mem hl
  exact h ri hri _ hmem

namespace HonRun

variable {μ r : ℕ} {target : E} {S : KeccakState} {root : Digest} {xs : List E}
  {os : List (List Opening)} {w : WhirEnd} {cfg : List Whir.Level} {Ls : List LvAt}
  (hR : HonRun μ r target S root xs os w cfg Ls)
include hR

/-- **Level `l`'s phase has an honest cap at the level's root**, whose halves `level_roots` holds. -/
theorem lqCapOk_os {cur tabs : E} {l : ℕ} (hl : l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length) :
    LqCapOk (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).depth (os.getD l []) ((hdOf μ r Ls).root l)
        (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).pd (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).capDepth ∧
      osRootA (hR.osHonest (cur := cur) (tabs := tabs)).own l = digestHalves ((hdOf μ r Ls).root l) := by
  have hlL : l < Ls.length := by rw [hR.len]; exact hl
  obtain ⟨hcdq, hpd, hcd2, hcdd, hQ⟩ := hR.cdpd hl
  have hidx := hR.run.phase_idx l hlL
  have hph := hR.run.phase_eq l hlL
  have hag := hR.br_ag l hl
  have hne := hR.br_q0 l hl
  have hps := hR.qs_lt hl
  obtain ⟨qs, ph, hq, hp, hlen, hok⟩ := hR.opens hl
  rw [hp] at hidx hph hag
  rw [hq] at hidx hag hne hps
  subst hidx hph
  have hlenQ : (os.getD l []).length = (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).queries := by
    have := LvAt.qs_length (Ls.getD l default) μ
    rw [hq, (hR.lvb hl).q] at this
    simpa using this
  have hcdo : Hints.capDepthOf (os.getD l []).length (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).depth =
      (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).capDepth := by
    rw [hlenQ, osCapDepth_eq hR.m11 hR.r4 hl]
  have hcl : ∀ o ∈ os.getD l [], o.leafIndex < 2 ^ (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).depth ∧
      o.path.length = (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).depth ∧
      climbD (merkleLeafDigest o.leaf) o.leafIndex o.path = (hdOf μ r Ls).root l := by
    intro o ho
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ho
    have hk' : k < ((os.getD l []).map Opening.leafIndex).length := by simpa using hk
    obtain ⟨-, h2, h3⟩ := openOne_facts (hok k hk' hk)
    simp only [List.getElem_map] at h3
    exact ⟨hps _ (List.mem_map_of_mem (List.getElem_mem hk)), h2, h3⟩
  rw [zip_map_self Opening.leafIndex (os.getD l [])] at hag
  have hc := lqCapHonest (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).depth (os.getD l []) ((hdOf μ r Ls).root l)
    (fun h => by rw [h] at hne; simp at hne) (by rw [hcdo]; exact hcd2) (by rw [hcdo]; exact hcdd) hcl hag
  rw [hcdo] at hc
  refine ⟨?_, (hdOf μ r Ls).rootA (honStatic_all _ _ hR.m11 hR.r4) hl⟩
  rw [hpd]
  exact hc


/-- **Level `l`'s honest `level_queries` call on the run's openings has its static facts**, with the
honest data's rounds and final coefficients, at any `λ`, windows and pointers. -/
theorem lqStatic_os {cur tabs : E} {l : ℕ} (hl : l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length) (lam : E)
    (wp : ℕ → ℕ) (icf ihs ipos iptr : ℕ) :
    (lqCall lam ((hdOf μ r Ls).root l) (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).depth
      (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).pd (os.getD l [])
      ((hR.osHonest (cur := cur) (tabs := tabs)).rounds l) ((hR.osHonest (cur := cur) (tabs := tabs)).hsv l)
      wp icf ihs ipos iptr).Static
      (oqQA (osCfgR (μ - minOpenLog) (r - 1)) l) (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).capDepth
      (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l) := by
  obtain ⟨hlen, hqs⟩ := hR.qs_os (cur := cur) (tabs := tabs) hl
  rw [← hlen]
  refine lqCall_static (hR.lqCapOk_os (cur := cur) (tabs := tabs) hl).1
    ((hR.osHonest (cur := cur) (tabs := tabs)).rounds_len l hl)
    ((hR.osHonest (cur := cur) (tabs := tabs)).hsv_len l hl) fun o ho => ?_
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ho
  have hk' : k < oqQA (osCfgR (μ - minOpenLog) (r - 1)) l := hlen ▸ hk
  obtain ⟨s1, s2, s3, s4⟩ := (hR.osHonest (cur := cur) (tabs := tabs)).static l hl k hk'
  have e0 : (os.getD l []).getD k ⟨0, [], []⟩ = (os.getD l [])[k]'hk := List.getD_eq_getElem (os.getD l []) ⟨0, [], []⟩ hk
  have e1 : ∀ f : Opening → List K, ((os.getD l []).map f).getD k [] = f ((os.getD l [])[k]'hk) := fun f => by
    rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map]
  have e2 : ∀ f : Opening → List Digest, ((os.getD l []).map f).getD k [] = f ((os.getD l [])[k]'hk) := fun f => by
    rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map]
  rw [hqs k hk', e0] at s1 s4
  rw [hR.rows_os (cur := cur) (tabs := tabs) hl k, e1] at s2 s4
  rw [hR.sibs_os (cur := cur) (tabs := tabs) hl k, e2, List.length_take] at s3
  exact ⟨s1, s2, by omega, s4⟩

/-- **Level `l`'s cap depth is the prover's at its phase.** -/
theorem capDepthOf_os {l : ℕ} (hl : l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length) :
    Hints.capDepthOf (os.getD l []).length (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).depth =
      (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).capDepth := by
  have hlL : l < Ls.length := by rw [hR.len]; exact hl
  have hidx := hR.run.phase_idx l hlL
  rw [hR.run.phase_eq l hlL] at hidx
  have := congrArg List.length hidx
  rw [List.length_map, LvAt.qs_length, (hR.lvb hl).q] at this
  rw [this, osCapDepth_eq hR.m11 hR.r4 hl]

/-- **Level `l`'s honest `level_queries` call pops the level's Merkle hints**, stream by stream. -/
theorem lqPops_os {cur tabs : E} {l : ℕ} (hl : l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length) (lam : E)
    (wp : ℕ → ℕ) (icf ihs ipos iptr : ℕ) :
    SameStreams ((lqCall lam ((hdOf μ r Ls).root l) (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).depth
      (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).pd (os.getD l [])
      ((hR.osHonest (cur := cur) (tabs := tabs)).rounds l) ((hR.osHonest (cur := cur) (tabs := tabs)).hsv l)
      wp icf ihs ipos iptr).pops (oqQA (osCfgR (μ - minOpenLog) (r - 1)) l) (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l))
      (Hints.levelHints (l == 0) (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).depth (os.getD l []).length
        (os.getD l [])) := by
  have hst := hR.lqStatic_os (cur := cur) (tabs := tabs) hl lam wp icf ihs ipos iptr
  obtain ⟨hlen, -⟩ := hR.qs_os (cur := cur) (tabs := tabs) hl
  obtain ⟨-, hpd, -, -, -⟩ := hR.cdpd hl
  obtain ⟨-, hbase, -⟩ := (hR.lvb hl).qsh
  obtain ⟨-, -, -, -, -, hW⟩ := hst
  rw [← hlen] at hW ⊢
  have hph : ∀ o ∈ os.getD l [], o.leaf.length = rowLen (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).base
      (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).folds ∧ (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).pd ≤ o.path.length := by
    intro o ho
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ho
    obtain ⟨-, w2, w3, -⟩ := hW k hk
    have e0 : opAt (os.getD l []) k = (os.getD l [])[k]'hk := List.getD_eq_getElem (os.getD l []) ⟨0, [], []⟩ hk
    simp only [lqCall, lqWs, e0, List.length_take] at w2 w3
    exact ⟨w2, by omega⟩
  refine lqCall_sameStreams ?_ ?_ (fun o ho => (hph o ho).1) (fun o ho => (hph o ho).2)
  · rw [hR.capDepthOf_os hl, hpd]
  · rw [oqSA, oq_base, hbase]
    unfold lvBase
    by_cases h : l = 0 <;> simp [h]

/-- **Level `l`'s `level_queries` specialization is in `lqTable`.** -/
theorem lqOk_os {l : ℕ} (hl : l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length) :
    LqOk (osCfgR (μ - minOpenLog) (r - 1)) l (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l) := by
  have hy := hR.yr
  by_cases hlt : l < (osCfgR (μ - minOpenLog) (r - 1)).yrLevel
  · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := hR.mid hlt
    exact h
  · have he : l = (osCfgR (μ - minOpenLog) (r - 1)).yrLevel := by omega
    subst he
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := hR.fin
    exact h

/-- **Level `l`'s phase has a query a level query.** -/
theorem phase_len_os {l : ℕ} (hl : l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length) :
    (os.getD l []).length = (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).queries := by
  have hlL : l < Ls.length := by rw [hR.len]; exact hl
  have hidx := hR.run.phase_idx l hlL
  rw [hR.run.phase_eq l hlL] at hidx
  have := congrArg List.length hidx
  rw [List.length_map, LvAt.qs_length, (hR.lvb hl).q] at this
  exact this

/-- **Level `l`'s `level_queries` completes placed on the run's openings** (`lqAG_all` at the honest
`lqCall`), at any second argument `li`, its pops the level's Merkle hints stream by stream. -/
theorem lqAt_os {cur tabs : E} {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} (kd : ℕ) {l : ℕ}
    (hl : l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length) (lam li : E) (wp : ℕ → ℕ) (icf ihs ipos iptr : ℕ)
    (R : ℕ → Prop)
    (hReg : (lqCall lam ((hdOf μ r Ls).root l) (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).depth
      (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).pd (os.getD l [])
      ((hR.osHonest (cur := cur) (tabs := tabs)).rounds l) ((hR.osHonest (cur := cur) (tabs := tabs)).hsv l)
      wp icf ihs ipos iptr).Reg (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).queries (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l) R)
    (fp c : ℕ) (hfc : fp + fs (osQueriesName (osCfgR (μ - minOpenLog) (r - 1)) l (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l)) ≤ c) :
    ∃ e, (∀ F, (∀ f, fs f ≤ F) → e ≤ c + ((osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).queries + 2) * (3 * F + 2048)) ∧
      CallAtA fs al cert kd (osQueriesName (osCfgR (μ - minOpenLog) (r - 1)) l (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l))
      [lam, li, ptrAt icf, ptrAt ihs, ptrAt ipos, ptrAt iptr]
      [(digestHalves ((hdOf μ r Ls).root l)).1, (digestHalves ((hdOf μ r Ls).root l)).2,
        ((lqCall lam ((hdOf μ r Ls).root l) (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).depth
          (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).pd (os.getD l [])
          ((hR.osHonest (cur := cur) (tabs := tabs)).rounds l) ((hR.osHonest (cur := cur) (tabs := tabs)).hsv l)
          wp icf ihs ipos iptr).oqG (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l)
          (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).queries (lvBase l)
          (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).capDepth 0 li).mret,
        lam ^ (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).queries] R
      (fun _ => False) (fun _ => True)
      ((lqCall lam ((hdOf μ r Ls).root l) (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).depth
        (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).pd (os.getD l [])
        ((hR.osHonest (cur := cur) (tabs := tabs)).rounds l) ((hR.osHonest (cur := cur) (tabs := tabs)).hsv l)
        wp icf ihs ipos iptr).Mem (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).queries
        (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).capDepth (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l))
      (fun rd t => SameStreams (t.pops coreProgram rd)
          (Hints.levelHints (l == 0) (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).depth (os.getD l []).length
            (os.getD l [])) ∧ t.Every (ExactAt coreProgram rd))
      (fs (osQueriesName (osCfgR (μ - minOpenLog) (r - 1)) l (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l))) fp c e := by
  have hq : oqQA (osCfgR (μ - minOpenLog) (r - 1)) l = (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).queries :=
    (hR.qs_os (cur := cur) (tabs := tabs) hl).1.symm.trans (hR.phase_len_os hl)
  have hA : LqAGE fs al cert kd (osQueriesName (osCfgR (μ - minOpenLog) (r - 1)) l (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l))
      (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).queries (lvBase l) (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).capDepth
      (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l) := by
    have h := lqAGE_all (fs := fs) (al := al) (cert := cert) kd _ _ _ _ _ _ _ _ _ _ _ (hR.lqOk_os hl)
    unfold oqSA
    rw [oqShapeOf_osOqName]
    exact h
  have hst := hR.lqStatic_os (cur := cur) (tabs := tabs) hl lam wp icf ihs ipos iptr
  have hpo := hR.lqPops_os (cur := cur) (tabs := tabs) hl lam wp icf ihs ipos iptr
  rw [hq] at hst hpo
  obtain ⟨e, hbe, he⟩ := hA _ li R hst hReg fp c hfc
  exact ⟨e, hbe, he.mono (fun _ h => h) (fun _ h => h) (fun _ h => h) (fun _ h => h)
    fun rd t _ h => ⟨by rw [h.1]; exact hpo, h.2⟩⟩

/-- **Level `l`'s `level_queries` returns the honest batch**, its second argument `1/λ` at a
non-final level. -/
theorem lqMret_os {cur tabs : E} {l : ℕ} (hl : l < (osCfgR (μ - minOpenLog) (r - 1)).levels.length) (lam li : E)
    (wp : ℕ → ℕ) (icf ihs ipos iptr : ℕ)
    (hli : l ≠ (osCfgR (μ - minOpenLog) (r - 1)).yrLevel → li = ((hR.osHonest (cur := cur) (tabs := tabs)).D l).lamInv) :
    ((lqCall lam ((hdOf μ r Ls).root l) (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).depth
      (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).pd (os.getD l [])
      ((hR.osHonest (cur := cur) (tabs := tabs)).rounds l) ((hR.osHonest (cur := cur) (tabs := tabs)).hsv l)
      wp icf ihs ipos iptr).oqG (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l)
      (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).queries (lvBase l)
      (osLvA (osCfgR (μ - minOpenLog) (r - 1)) l).capDepth 0 li).mret =
      ((hR.osHonest (cur := cur) (tabs := tabs)).D l).batched := by
  obtain ⟨hlen, hqs⟩ := hR.qs_os (cur := cur) (tabs := tabs) hl
  obtain ⟨-, hbase, -⟩ := (hR.lvb hl).qsh
  have hb : (oqSA (osCfgR (μ - minOpenLog) (r - 1)) l).base = lvBase l := by rw [oqSA, oq_base, hbase]
  rw [lq_mret_eq, (hR.osHonest (cur := cur) (tabs := tabs)).batched_eq l hl]
  split_ifs with hf
  · rfl
  · rw [hli fun he => hf ((hR.final_iff hl).2 he)]
    refine oqChain_congr (fun h => ?_) _ fun k hk => ?_
    · rw [hb]
      by_cases h0 : l = 0
      · simp [lvBase, h0]
      · simp [lqOdd, lvBase, h0] at h
    · have hk' : k < (os.getD l []).length := by
        rw [hlen]; exact hk
      have er : ((os.getD l []).map (·.leaf)).getD k [] = (opAt (os.getD l []) k).leaf := by
        rw [List.getD_eq_getElem _ _ (by simpa using hk'), List.getElem_map, opAt,
          List.getD_eq_getElem (os.getD l []) ⟨0, [], []⟩ hk']
      rw [hR.rows_os (cur := cur) (tabs := tabs) hl k, hqs k (by rw [← hlen]; exact hk'), er]
      rfl

end HonRun

end
end LeanVM.Guest.B1.Whir
