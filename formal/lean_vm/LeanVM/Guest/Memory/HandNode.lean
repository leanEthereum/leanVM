/-
  LeanVM.Guest.Memory.HandNode

  `main`'s cost from a family with hand functions: `da_verify`'s and the children's loop's bounds
  the node's constants `C₁`, `C₂` (`certAt`), `main`'s raised by them (`handAt`, by `statB_shift`),
  the check with hand functions at them (`checkedH_at`), and `main`'s tree within its inner bound
  plus `C₁ + C₂` (`mainCost_le`), the loop's run by `loopRun_cost_le`.
-/

module

public import LeanVM.Guest.Memory.FamilyHand
public import LeanVM.Guest.Memory.StaticShift

/-!
# `main` and the node's constants

A family with hand functions (`Memory/FamilyHand.lean`) certifies `da_verify` and the children's loop
`__loop4_main` at the bound `0`: their words are the node's (its blob rows, its children's lists),
which `main`'s values do not name. `main`, their only caller, is checked against those zeros; raising
them to the node's `C₁`, `C₂` (`certAt`) raises `main`'s bound by `C₁ + C₂` (`statB_shift`, one site
each), so the family gives the check with hand functions at every `C₁`, `C₂` (`checkedH_at`). Then
`main`'s tree costs at most its inner bound at its virtual parameters' values plus `C₁ + C₂`
(`mainCost_le`), given every node of its callees but the loop with its hand fact (`da_verify`'s says
its words are within `C₁`), and the loop's run with its iterations' sum within `C₂` (`LoopRun`).
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest

@[expose] public section

/-- The certificates with the node's constants: `da_verify`'s (index `jd`) `C₁`, the loop's (`jl`) `C₂`. -/
def certAt (cert : ℕ → Cert) (jd jl C₁ C₂ : ℕ) (j : ℕ) : Cert :=
  if j = jd then .stat [] ⟨C₁, []⟩ [] else if j = jl then .stat [] ⟨C₂, []⟩ [] else cert j

/-- A hand's inner bound raised by `d`. -/
def Hand.raise (h : Hand) (d : ℕ) : Hand := ⟨h.vps, h.pre, ⟨h.b.c + d, h.b.cs⟩, h.ks⟩

/-- The hands with `main`'s (index `jm`) raised by `d`. -/
def handAt (hand : ℕ → Option Hand) (jm d : ℕ) (j : ℕ) : Option Hand :=
  if j = jm then (hand j).map (·.raise d) else hand j

/-- The node's constants as weights of `main`'s call sites. -/
def nodeδ (C₁ C₂ : ℕ) (g : String) : ℕ :=
  C₁ * (if g = "da_verify" then 1 else 0) + C₂ * (if g = "__loop4_main" then 1 else 0)

/-- **The family's facts about `main` (`jm`), `da_verify` (`jd`) and the loop (`jl`)**, each by the
kernel: their names, `main` their only caller (and the loop itself), their bounds `0`, `da_verify` a
hand, `main` checked on its body (no selector split) and calling each once. -/
structure NodeIdx (cert : ℕ → Cert) (hand : ℕ → Option Hand) (lh : ℕ → Option (Hand × Option ℕ))
    (abs : ℕ → Bool) (jm jd jl : ℕ) : Prop where
  hm : jm < coreProgram.length
  hl : jl < coreProgram.length
  nm : (coreProgram[jm]?).map Fn.name = some "main"
  nd : (coreProgram[jd]?).map Fn.name = some "da_verify"
  nl : (coreProgram[jl]?).map Fn.name = some "__loop4_main"
  callers : ∀ j < coreProgram.length, j ≠ jm → j ≠ jl → jd ∉ Data.calleesJ j ∧ jl ∉ Data.calleesJ j
  loopd : jd ∉ Data.calleesJ jl
  certd : cert jd = .stat [] ⟨0, []⟩ []
  certl : cert jl = .stat [] ⟨0, []⟩ []
  handd : (hand jd).isSome = true
  handm : (hand jm).isSome = true
  lhl : (lh jl).isSome = true
  absm : abs jm = false
  lhm : lh jm = none
  absl : abs jl = false
  topm : topSel (coreProgram[jm]'hm).body = none
  sitesd : sitesL (nodeδ 1 0) (coreProgram[jm]'hm).body = 1
  sitesl : sitesL (nodeδ 0 1) (coreProgram[jm]'hm).body = 1

/-- `Tree.KidsValid` of appended calls splits. -/
theorem kidsValid_splitA {P : Core.Program} {rd : Reader} {σ : Val} : ∀ {cs cs' : List Call} {ks : List Tree},
    Tree.KidsValid P rd σ (cs ++ cs') ks →
      ∃ ks₁ ks₂, ks = ks₁ ++ ks₂ ∧ Tree.KidsValid P rd σ cs ks₁ ∧ Tree.KidsValid P rd σ cs' ks₂
  | [], _, ks, h => ⟨[], ks, rfl, by simp [Tree.KidsValid], h⟩
  | c :: cs, cs', [], h => h.elim
  | c :: cs, cs', k :: ks, ⟨hn, hc, h⟩ => by
      obtain ⟨ks₁, ks₂, rfl, h1, h2⟩ := kidsValid_splitA h
      exact ⟨k :: ks₁, ks₂, rfl, ⟨hn, hc, h1⟩, h2⟩

section LoopHandA

variable {P : Core.Program} {cert : String → Cert} {ω : String → ℕ} {rd : Reader}

/-- **A loop hand's run within its iterations' sum**, counting words or not (`α`): `loopRun_cost_le`'s. -/
theorem loopRun_cost_leA {α : Bool} {look : String → Cert} {wl : String → Option ℕ} (hlook : LookOk look cert)
    (hwl : WlOk wl ω) {f : String} {fn : Fn} (hf : P.find? f = some fn) {h : Hand} {endc : Option ℕ}
    (hc : chkHandL look wl α h endc (ω f) fn = true) {Q : Tree → Prop}
    (hQ : ∀ k, Q k → ∀ args' rets', k.Valid P rd args' rets' → k.BufsOk P → Bound P α cert ω k args')
    {t : Tree} {S : ℕ} (hrun : LoopRun f fn.params h (ω f) Q t S) :
    ∀ {args rets : List E}, t.Valid P rd args rets → t.BufsOk P → t.cost P α ω ≤ S := by
  have hname := fn_name_of_find hf
  unfold chkHandL at hc
  split at hc
  · rename_i pre hsh
    split at hc
    · rename_i r hb
      simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
      obtain ⟨hle, hpreS⟩ := hc
      obtain ⟨c, i', p0, prest, hps, hbody, hnr, hst, x, y, hadd, hxy⟩ := loopShape_spec hsh
      rw [blockR_eq] at hb
      replace hb := blockB_mono hlook _ _ hb
      rw [hname] at hbody
      induction hrun with
      | last σ => intro _ _ hv; exact hv.elim
      | @step σ bufs ks tk S hks hpre htk ih =>
          intro args rets hv hbo
          have hbk : Tree.BufsOkKids P (ks ++ [tk]) := by simp only [Tree.BufsOk] at hbo; exact hbo.2
          obtain ⟨fn', hf', hp, es, vs, hw, hr, hes, hk⟩ := hv
          rw [hf] at hf'
          cases hf'
          have hcost : (Tree.node f σ bufs (ks ++ [tk])).cost P α ω =
              ω f + aw α σ es + Tree.costKids P α ω (ks ++ [tk]) := by
            rw [Tree.cost]
            simp only [Tree.events, Tree.name, Tree.val, hf, hw, aw]
          rw [hbody, walk_append] at hw
          rcases walk_noRet (σ := σ) pre hnr with ⟨es1, hw1⟩ | hw1
          · rw [hw1] at hw
            have hwt : walk σ [.callIf c f (i' :: prest), .ret []] =
                .ret [.inK c, if σ c = 0 then .skip f (i' :: prest) else .call f (i' :: prest) []] [] := by
              simp [walk, walk1, Out.seq, Out.pre]
            rw [hwt] at hw
            simp only [Out.seq, Out.pre, Out.ret.injEq] at hw
            obtain ⟨rfl, rfl⟩ := hw
            have hes1 : HoldsAll rd σ es1 := fun e he => hes e (List.mem_append_left _ he)
            rw [calls_append] at hk
            obtain ⟨ks1, ks2, hks12, hk1, hk2⟩ := kidsValid_splitA hk
            have hcalls : calls [Ev.inK c, if σ c = 0 then .skip f (i' :: prest)
                else .call f (i' :: prest) []] = [⟨f, i' :: prest, [], !decide (σ c = 0)⟩] := by
              by_cases h0c : σ c = 0 <;> simp only [h0c, ↓reduceIte, decide_true, decide_false,
                Bool.not_true, Bool.not_false] <;> rfl
            rw [hcalls] at hk2
            match ks2, hk2 with
            | [tk2], ⟨htn, htv, _⟩ =>
              obtain ⟨rfl, hl⟩ := List.append_inj' hks12 rfl
              simp only [List.cons.injEq, and_true] at hl
              subst hl
              obtain ⟨hbk1, hbk2⟩ := bufsOkKids_split ks [tk] hbk
              have hp' : (fn.params ++ h.vps).map σ = args ++ h.vps.map σ := by
                rw [List.map_append, hp]
              have hpre' : ArgsPre h.pre (args ++ h.vps.map σ) := by rw [← hp']; exact hpre
              have hkb := blockB_sound (rd := rd) (ω := ω) hp' hwl pre ([], []) r
                ⟨fun _ h => (List.not_mem_nil h).elim, fun _ h => (List.not_mem_nil h).elim⟩ hb
                (fun q hq => hpre' q (hpreS q hq))
                (by rw [hw1]; exact hes1) ks (by rw [hw1]; exact hk1) hbk1
                (fun k hk' => hQ k (hks k hk'))
              rw [hw1] at hkb
              simp only [Out.evs] at hkb
              have hle' := Aff.eval_le_of_leB hle (args ++ h.vps.map σ)
              simp only [Aff.eval] at hle' hkb
              have htail : aw α σ [Ev.inK c, if σ c = 0 then .skip f (i' :: prest)
                  else .call f (i' :: prest) []] = 0 := by
                unfold aw allocs; split_ifs <;> rfl
              have hS : tk.cost P α ω ≤ S := by
                by_cases h0c : σ c = 0
                · simp only [h0c, decide_true, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at htv
                  obtain ⟨⟨g', σ', rfl⟩, -⟩ := htv
                  cases htk with
                  | last => rw [Tree.cost]; split <;> omega
                · simp only [h0c, decide_false, Bool.not_false, ↓reduceIte] at htv
                  exact ih htv (by simp only [Tree.BufsOkKids] at hbk2; exact hbk2.1)
              rw [hcost, aw_append, htail, costKids_append, Tree.costKids, Tree.costKids, hp']
              unfold Aff.eval
              omega
          · rw [hw1] at hw; simp [Out.seq] at hw
    · cases hc
  · cases hc

end LoopHandA

variable {α : Bool} {cert : ℕ → Cert} {hand : ℕ → Option Hand} {lh : ℕ → Option (Hand × Option ℕ)}
  {abs : ℕ → Bool} {om : ℕ → ℕ} {jm jd jl : ℕ}

theorem nodeδ_eq (C₁ C₂ : ℕ) : nodeδ C₁ C₂ = fun g => C₁ * nodeδ 1 0 g + C₂ * nodeδ 0 1 g := by
  funext g; unfold nodeδ; split_ifs <;> simp

theorem sitesL_nodeδ (hI : NodeIdx cert hand lh abs jm jd jl) (C₁ C₂ : ℕ) :
    sitesL (nodeδ C₁ C₂) (coreProgram[jm]'hI.hm).body = C₁ + C₂ := by
  rw [nodeδ_eq, sitesL_add (fun g => C₁ * nodeδ 1 0 g) (fun g => C₂ * nodeδ 0 1 g), sitesL_mul, sitesL_mul,
    hI.sitesd, hI.sitesl]
  omega

theorem name_idx {j : ℕ} {g : String} (h : (coreProgram[j]?).map Fn.name = some g) :
    j < coreProgram.length ∧ coreIdx g = j := by
  refine ⟨?_, coreIdx_of_name h⟩
  rcases hj : coreProgram[j]? with _ | fn
  · rw [hj] at h; cases h
  · exact (List.getElem?_eq_some_iff.mp hj).1

/-- A callee's index names it, so it is `jd` or `jl` only as `da_verify` or the loop. -/
theorem callee_eq {j k : ℕ} {g : String} (hk : calleeIdx j g = some k) : coreIdx g = k :=
  coreIdx_of_name (calleeIdx_spec hk)

theorem calleeIdx_mem {j k : ℕ} {g : String} (hk : calleeIdx j g = some k) : k ∈ Data.calleesJ j := by
  unfold calleeIdx at hk; exact List.mem_of_find?_eq_some hk

/-- **The shifted lookup of `main`'s callees.** -/
theorem shiftOk_main (hI : NodeIdx cert hand lh abs jm jd jl) (C₁ C₂ : ℕ) :
    ShiftOk (lookS cert jm) (lookS (certAt cert jd jl C₁ C₂) jm) (nodeδ C₁ C₂) := by
  intro g
  unfold lookS
  rcases hk : calleeIdx jm g with _ | k
  · left; rfl
  · have hgk := callee_eq hk
    by_cases hd : k = jd
    · right
      subst hd
      have hg : g = "da_verify" := by
        have := calleeIdx_spec hk; rw [hI.nd] at this; exact (Option.some.inj this).symm
      refine ⟨[], 0, [], [], hI.certd, ?_⟩
      simp [certAt, nodeδ, hg]
    · by_cases hl : k = jl
      · right
        subst hl
        have hg : g = "__loop4_main" := by
          have := calleeIdx_spec hk; rw [hI.nl] at this; exact (Option.some.inj this).symm
        refine ⟨[], 0, [], [], hI.certl, ?_⟩
        simp [certAt, nodeδ, hg, hd]
      · left; simp [certAt, hd, hl]

/-- Off `main`, the shifted lookups are the family's. -/
theorem lookS_certAt {j : ℕ} (hj : j < coreProgram.length) (hI : NodeIdx cert hand lh abs jm jd jl)
    (hjm : j ≠ jm) (hjl : j ≠ jl) (C₁ C₂ : ℕ) : lookS (certAt cert jd jl C₁ C₂) j = lookS cert j := by
  funext g
  unfold lookS
  rcases hk : calleeIdx j g with _ | k
  · rfl
  · have hm := calleeIdx_mem hk
    obtain ⟨h1, h2⟩ := hI.callers j hj hjm hjl
    have : k ≠ jd := fun h => h1 (h ▸ hm)
    have : k ≠ jl := fun h => h2 (h ▸ hm)
    simp [certAt, *]

/-- **The check with hand functions at the node's constants.** -/
theorem checkedH_at (hr : RangeOk (chkHJ α cert hand lh abs om) 0 coreProgram.length) {ω : String → ℕ}
    (hω : ∀ j (hj : j < coreProgram.length), ω coreProgram[j].name = om j)
    (hI : NodeIdx cert hand lh abs jm jd jl) (C₁ C₂ : ℕ) :
    CheckedH coreProgram α (fun g => certAt cert jd jl C₁ C₂ (coreIdx g)) ω
      (fun g => handAt hand jm (C₁ + C₂) (coreIdx g))
      (fun g => abs (coreIdx g) = true ∨ (lh (coreIdx g)).isSome = true) := by
  intro fn hfn hA
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hfn
  have hc := RangeOk.all hr hj
  simp only [coreIdx_getElem hj] at hA ⊢
  refine ⟨lookS (certAt cert jd jl C₁ C₂) j, omLookS om j, lookS_ok _ j, omLookS_ok hω j, ?_⟩
  have habs : abs j = false := by cases h : abs j <;> simp_all
  have hlh : lh j = none := by cases h : lh j <;> simp_all
  unfold chkHJ at hc
  rw [habs, hlh, Bool.false_or] at hc
  rw [hω j hj]
  by_cases hjm : j = jm
  · subst hjm
    obtain ⟨h, hh⟩ := Option.isSome_iff_exists.mp hI.handm
    simp only [handAt, ↓reduceIte, hh, Option.map_some]
    rw [hh] at hc
    unfold chkHand at hc ⊢
    have hst : statB (lookS cert j) (omLookS om j) α h.pre h.b h.ks (om j) (coreProgram[j].withVps h.vps)
        coreProgram[j].body = true := by
      rcases Bool.or_eq_true_iff.mp hc with h1 | h1
      · exact h1
      · unfold selSplit at h1; rw [hI.topm] at h1; cases h1
    have := statB_shift (shiftOk_main hI C₁ C₂) hst
    rw [sitesL_nodeδ hI] at this
    rw [Bool.or_eq_true]; left
    exact this
  · have hjl : j ≠ jl := by
      intro h; subst h; rw [hlh] at hA; have := hI.lhl; rw [hlh] at this; cases this
    rw [lookS_certAt hj hI hjm hjl]
    simp only [handAt, hjm, ↓reduceIte]
    cases hh : hand j with
    | none =>
        rw [hh] at hc
        have hjd : j ≠ jd := by intro h; subst h; have := hI.handd; rw [hh] at this; cases this
        simp only [certAt, hjd, hjl, ↓reduceIte]
        exact hc
    | some h => rw [hh] at hc; exact hc

theorem jd_ne_jl (hI : NodeIdx cert hand lh abs jm jd jl) : jd ≠ jl := by
  intro h; have := hI.nd; rw [h, hI.nl] at this; exact absurd (Option.some.inj this) (by decide)

/-- A function found by name is the one at that name's index. -/
theorem find?_idx {j : ℕ} {g : String} {fn : Fn} (hf : coreProgram.find? g = some fn)
    (hn : (coreProgram[j]?).map Fn.name = some g) (hj : j < coreProgram.length) : fn = coreProgram[j] := by
  have hname : fn.name = g := fn_name_of_find hf
  have hf' : List.find? (fun f => f.name == g) coreProgram = some fn := hf
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp (List.mem_of_find?_eq_some hf')
  have h1 := coreIdx_getElem hi
  rw [hname, coreIdx_of_name hn] at h1
  subst h1
  rfl

/-- `Bound` reads a certificate at the tree's name only. -/
theorem bound_congr {P : Core.Program} {α : Bool} {c c' : String → Cert} {ω : String → ℕ} {t : Tree}
    {args : List E} (h : c t.name = c' t.name) (hb : Bound P α c ω t args) : Bound P α c' ω t args := by
  unfold Bound at hb ⊢; rw [← h]; exact hb

/-- **`main`'s tree within its inner bound plus the node's constants**: every node of its callees but
the loop with its hand fact, and the loop's run with its iterations' sum within `C₂`. -/
theorem mainCost_le (hr : RangeOk (chkHJ α cert hand lh abs om) 0 coreProgram.length) {ω : String → ℕ}
    (hω : ∀ j (hj : j < coreProgram.length), ω coreProgram[j].name = om j)
    (hI : NodeIdx cert hand lh abs jm jd jl) (C₁ C₂ : ℕ) {h : Hand} (hh : hand jm = some h) {hl : Hand}
    {endc : Option ℕ} (hlj : lh jl = some (hl, endc)) {rd : Reader} {σ : Val} {bufs : List ℕ}
    {kids : List Tree} {args rets : List E}
    (hv : (Tree.node "main" σ bufs kids).Valid coreProgram rd args rets)
    (hb : (Tree.node "main" σ bufs kids).BufsOk coreProgram)
    (hkids : ∀ k ∈ kids, k.name = "__loop4_main" ∨
      k.Every (HandFact coreProgram (fun g => certAt cert jd jl C₁ C₂ (coreIdx g))
        (fun g => handAt hand jm (C₁ + C₂) (coreIdx g))
        (fun g => abs (coreIdx g) = true ∨ (lh (coreIdx g)).isSome = true)))
    (hloop : ∀ k ∈ kids, k.name = "__loop4_main" → ∀ a r, k.Valid coreProgram rd a r → ∃ S,
      LoopRun "__loop4_main" (coreProgram[jl]'hI.hl).params hl (ω "__loop4_main")
        (fun k => k.Every (HandFact coreProgram (fun g => certAt cert jd jl C₁ C₂ (coreIdx g))
          (fun g => handAt hand jm (C₁ + C₂) (coreIdx g))
          (fun g => abs (coreIdx g) = true ∨ (lh (coreIdx g)).isSome = true))) k S ∧ S ≤ C₂)
    (hpre : ArgsPre h.pre (args ++ h.vps.map σ)) :
    (Tree.node "main" σ bufs kids).cost coreProgram α ω ≤ h.b.eval (args ++ h.vps.map σ) + (C₁ + C₂) := by
  have hchk := checkedH_at hr hω hI C₁ C₂
  have hbk : Tree.BufsOkKids coreProgram kids := by simp only [Tree.BufsOk] at hb; exact hb.2
  obtain ⟨fn, hf, hp, es, vs, hw, -, hes, hk⟩ := hv
  have hjm := (name_idx hI.nm).2
  have hjl := (name_idx hI.nl).2
  obtain ⟨look, wl, hlook, hwl, hc⟩ := hchk fn (List.mem_of_find?_eq_some (show List.find? _ coreProgram = _ from hf))
    (by simp [fn_name_of_find hf, hjm, hI.absm, hI.lhm])
  simp only [fn_name_of_find hf, hjm, handAt, ↓reduceIte, hh, Option.map_some] at hc
  have hpre' : ArgsPre (h.raise (C₁ + C₂)).pre (args ++ (h.raise (C₁ + C₂)).vps.map σ) := hpre
  have hmain := hand_node_le (bufs := bufs) hlook hwl hf hp hw hes hk hbk ?_ hc hpre'
  · have : (h.raise (C₁ + C₂)).b.eval (args ++ (h.raise (C₁ + C₂)).vps.map σ) =
        h.b.eval (args ++ h.vps.map σ) + (C₁ + C₂) := by
      simp only [Hand.raise, Aff.eval]; omega
    exact hmain.trans (le_of_eq this)
  intro k hkm a r hvk hbkk
  rcases hkids k hkm with hn | hev
  · -- the children's loop: its run within `C₂`
    obtain ⟨S, hrun, hS⟩ := hloop k hkm hn a r hvk
    have hcl := loopHand_checked hr hI.hl hlj hI.absl
    rw [← hω jl hI.hl] at hcl
    have hnl : (coreProgram[jl]'hI.hl).name = "__loop4_main" := by
      have := hI.nl; rw [List.getElem?_eq_getElem hI.hl] at this; exact Option.some.inj this
    rw [hnl] at hcl
    have hfl : coreProgram.find? "__loop4_main" = some (coreProgram[jl]'hI.hl) := by
      obtain ⟨fnl, hfl, -⟩ : ∃ fnl, coreProgram.find? k.name = some fnl ∧ True := by
        cases k with
        | node f σ' b' ks' => obtain ⟨fnl, hfl, -⟩ := hvk; exact ⟨fnl, hfl, trivial⟩
        | phantom => exact hvk.elim
      rw [hn] at hfl
      rw [hfl, find?_idx hfl hI.nl hI.hl]
    let certX : String → Cert := fun g =>
      if g = "__loop4_main" then .stat [] ⟨0, []⟩ [] else certAt cert jd jl C₁ C₂ (coreIdx g)
    have hlookX : LookOk (lookS cert jl) certX := by
      intro g hg
      unfold lookS at hg ⊢
      rcases hk' : calleeIdx jl g with _ | k'
      · rw [hk'] at hg; exact absurd rfl hg
      · have hgk := callee_eq hk'
        have hmem := calleeIdx_mem hk'
        simp only [certX]
        by_cases hgl : g = "__loop4_main"
        · subst hgl; rw [hjl] at hgk; subst hgk; simp [hI.certl]
        · have hk'l : k' ≠ jl := by intro e; subst e; exact hgl (by
            have := calleeIdx_spec hk'; rw [hI.nl] at this; exact (Option.some.inj this).symm)
          have hk'd : k' ≠ jd := fun e => hI.loopd (e ▸ hmem)
          simp [hgl, hgk, certAt, hk'd, hk'l]
    have hQ : ∀ k, (fun k => k.Every (HandFact coreProgram (fun g => certAt cert jd jl C₁ C₂ (coreIdx g))
          (fun g => handAt hand jm (C₁ + C₂) (coreIdx g))
          (fun g => abs (coreIdx g) = true ∨ (lh (coreIdx g)).isSome = true))) k →
        ∀ args' rets', k.Valid coreProgram rd args' rets' → k.BufsOk coreProgram →
          Bound coreProgram α certX ω k args' := by
      intro k hev args' rets' hv' hb'
      have hB := chk_soundH hchk k.count k args' rets' le_rfl hv' hb' hev
      cases k with
      | phantom => exact hv'.elim
      | node f σ' b' ks' =>
          refine bound_congr ?_ hB
          have hnot := hev.1.1
          simp only [Tree.name, certX]
          have : f ≠ "__loop4_main" := by
            intro e; apply hnot; right; rw [e, hjl, hlj]; rfl
          simp [this]
    have hcost := loopRun_cost_leA (cert := certX) hlookX (omLookS_ok hω jl) hfl hcl hQ hrun hvk hbkk
    unfold Bound
    rw [hn]
    simp only [hjl, certAt, (jd_ne_jl hI).symm, ↓reduceIte]
    intro _
    simp only [Aff.eval, List.map_nil, List.sum_nil, Nat.add_zero]
    omega
  · exact chk_soundH hchk k.count k a r le_rfl hvk hbkk hev

end
end LeanVM.Guest.Memory
