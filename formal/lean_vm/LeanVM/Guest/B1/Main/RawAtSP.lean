/-
  LeanVM.Guest.B1.Main.RawAtSP

  `main_loop3` (leanSPHINCS) placed with its pops (`CompleteAtDP`), from `verify_sig_lean_sphincs` placed with its pops (`VerifySigP`): each iteration its raw index, then its signature's check's entries (`Sig.spSegPops`), iteration by iteration.
-/

module

public import LeanVM.Guest.B1.Main.RawAt
public import LeanVM.Guest.B1.Main.CompleteP
public import LeanVM.Guest.B1.Sig.SphincsSigPops
public import LeanVM.Guest.B1.Main.CompleteE

/-!
# `main_loop3`, placed with its pops

`RawAt`'s proof of `rawS_relIn` with the trees (`relAtInP_of_walk_loop`), its call of `verify_sig_lean_sphincs` placed by `VerifySigP`.

* `VerifySigP fs cert nV`: `verify_sig_lean_sphincs`, on the hypotheses of `Lift.verify_sig_lean_sphincs_relIn`, is placed at every frame pointer in `nV` words by a tree popping `Sig.spSegPops`;
* `l4Pops D j`: iteration `j`'s entries, its raw index `g^(slot j)` then the check's;
* `VerifySigPQ fs cert nV Q`: `VerifySigP` by a tree whose every node satisfies `Q`;
* `rawS_stepPQ`, `rawS_loopPQ`, `rawS_completeAtDPQ`: an iteration, the loop from `g^j`, popping iterations `j ..< nrs`' entries in order, every node satisfying `Q` (`main_loop3`'s own nodes by `hq`); `rawS_stepP`, `rawS_loopP`, `rawS_completeAtDP` at `Q` trivial.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1 (LowDef CompleteAtDP Returns disj_nil)
open LeanVM.Guest.B1.Digest
open LeanVM.Guest.B1.Da (SlOk slEvs_holds limb0_gen_pow_mul)

@[expose] public section

/-- **`verify_sig_lean_sphincs` placed with its pops**: on `Lift.verify_sig_lean_sphincs_relIn`'s hypotheses, at every frame pointer, in `nV` words, by a tree popping `Sig.spSegPops`. -/
def VerifySigP (fs : String → ℕ) (cert : String → V → ℕ) (nV : ℕ) : Prop :=
  ∀ (rd : Reader) (R : ℕ → Prop) (p bb : E) (pk : Sphincs.PublicKey) (m : HashSig.Message) (sig : Sphincs.Signature),
    Sig.MemOK rd 256 → Sig.ByteBits rd bb →
    Sig.ClaimAt rd p (Sig.cellOf128 pk.publicSeed) (Sig.cellOf128 pk.root) (Sig.cellOf128 (m.extractLsb' 0 128))
      (Sig.cellOf128 (m.extractLsb' 128 128)) →
    Sphincs.verifyWithKeccak pk m sig = true →
    (∀ k < 4, ∃ i, p.limb 0 * addressOfIndex k = addressOfIndex i ∧ R i) →
    (∀ v < 256, ∃ i, bb.limb 0 * addressOfIndex v = addressOfIndex i ∧ R i) →
    ∀ fp, RelAtInP coreProgram fs cert rd R (fun _ => False) fp nV "verify_sig_lean_sphincs" [p, bb] []
      (Sig.spSegPops pk m sig)

/-- **`VerifySigP` by a tree whose every node satisfies `Q rd`.** -/
def VerifySigPQ (fs : String → ℕ) (cert : String → V → ℕ) (nV : ℕ) (Q : Reader → String → Val → Prop) : Prop :=
  ∀ (rd : Reader) (R : ℕ → Prop) (p bb : E) (pk : Sphincs.PublicKey) (m : HashSig.Message) (sig : Sphincs.Signature),
    Sig.MemOK rd 256 → Sig.ByteBits rd bb →
    Sig.ClaimAt rd p (Sig.cellOf128 pk.publicSeed) (Sig.cellOf128 pk.root) (Sig.cellOf128 (m.extractLsb' 0 128))
      (Sig.cellOf128 (m.extractLsb' 128 128)) →
    Sphincs.verifyWithKeccak pk m sig = true →
    (∀ k < 4, ∃ i, p.limb 0 * addressOfIndex k = addressOfIndex i ∧ R i) →
    (∀ v < 256, ∃ i, bb.limb 0 * addressOfIndex v = addressOfIndex i ∧ R i) →
    ∀ fp, RelAtInPE coreProgram fs cert rd (Q rd) R (fun _ => False) fp nV "verify_sig_lean_sphincs" [p, bb] []
      (Sig.spSegPops pk m sig)

theorem VerifySigPQ.toP {fs : String → ℕ} {cert : String → V → ℕ} {nV : ℕ} {Q : Reader → String → Val → Prop}
    (h : VerifySigPQ fs cert nV Q) : VerifySigP fs cert nV :=
  fun rd R p bb pk m sig hm hbb hat hv hreg hregb fp => (h rd R p bb pk m sig hm hbb hat hv hreg hregb fp).toP

theorem VerifySigP.toPQ {fs : String → ℕ} {cert : String → V → ℕ} {nV : ℕ} (h : VerifySigP fs cert nV) :
    VerifySigPQ fs cert nV fun _ _ _ => True :=
  fun rd R p bb pk m sig hm hbb hat hv hreg hregb fp =>
    (h rd R p bb pk m sig hm hbb hat hv hreg hregb fp).withEvery fun t _ _ => Tree.every_true t

/-- **Iteration `j`'s entries**: its raw index, then its signature's check's. -/
def l4Pops {nrs Y X nrx cv tb bb : ℕ} {Lin : Layout} (D : RawSData nrs Y X nrx cv tb bb Lin) (j : ℕ) : List Pop :=
  ("sp_raw_index", [gen ^ D.slot j]) :: Sig.spSegPops (D.pk j) (D.msg j) (D.sig j)

theorem main_loop3_loop : coreProgram.loop name% «main_loop3» = true := by
  rw [Program.loop_of_find? l4_find, Fn.loop, l4_body, Da.fn_name_of_find l4_find]
  rfl

/-- `main_loop3`'s statements before its call of `verify_sig_lean_sphincs`. -/
def l4A : List Stmt := l4Pre.take 10

/-- `main_loop3`'s statements between its two calls. -/
def l4B : List Stmt := (l4Pre.drop 11).take 5

/-- `main_loop3`'s self-call. -/
def l4Call : Stmt := .callIf (.n 20) name% «main_loop3» [.n 22, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6]

theorem l4Pre_split : l4Pre = l4A ++ [.call "verify_sig_lean_sphincs" [.n 17, .n 6] []] ++ l4B ++ [l4Call] := rfl

theorem l4A_atoms : Sig.atomsOnly l4A = true := rfl
theorem l4B_atoms : Sig.atomsOnly l4B = true := rfl
theorem l4A_pops (rd : Reader) (σ : Val) : Sig.atomsPops rd σ l4A = [("sp_raw_index", [σ (.n 7)])] := rfl
theorem l4B_pops (rd : Reader) (σ : Val) : Sig.atomsPops rd σ l4B = [] := rfl

theorem splicePops_callIf {rd : Reader} {σ : Val} (c : V) (f : String) (args : List V) (k : List Pop) :
    SplicePops rd σ [.callIf c f args] [k] k := by
  refine ⟨[.inK c, if σ c = 0 then .skip f args else .call f args []], ?_, ?_, ?_⟩
  · simp [walk, walk1, Out.seq, Out.pre]
  · split <;> rfl
  · split <;> simp [splice]

/-- **One iteration of `main_loop3`, placed, with its pops, every node satisfying `Q`**: its raw index and its
check's, then its tail's `pt` (`[]` after the last). -/
theorem rawS_stepPQ (fs : String → ℕ) (cert : String → V → ℕ) {nV : ℕ} {Q : Reader → String → Val → Prop}
    (hV : VerifySigPQ fs cert nV Q)
    {nrs Y X nrx cv tb bb : ℕ} {Lin : Layout} (D : RawSData nrs Y X nrx cv tb bb Lin) (hY : Y ≤ 2 ^ 23)
    (hnrs : nrs < 2 ^ 34) {rd : Reader} (hl : LowDef 23 rd) (hL : MemL rd Lin)
    (hq : ∀ σ es vs, walk σ (coreProgram.getD idx% «main_loop3» default).body = .ret es vs →
      (∀ e ∈ es, e.Holds rd σ) → Q rd name% «main_loop3» σ) {j : ℕ} (hj : j < nrs)
    {fp c Bt m : ℕ} {pt : List Pop}
    (htail : if j + 1 < nrs then
        RelAtInCPE coreProgram fs cert rd (Q rd) (RegionL Lin) (RegionL []) (fp + fs name% «main_loop3») (c + nV) Bt m
          name% «main_loop3» [gen ^ (j + 1), gen ^ nrs, gen ^ Y, gen ^ (cv + X), gen ^ nrx, gen ^ tb, gen ^ bb] [] pt
      else Bt = fs name% «main_loop3» ∧ m = 0 ∧ pt = []) :
    RelAtInCPE coreProgram fs cert rd (Q rd) (RegionL Lin) (RegionL []) fp c (fs name% «main_loop3» + Bt) (nV + m)
      name% «main_loop3» [gen ^ j, gen ^ nrs, gen ^ Y, gen ^ (cv + X), gen ^ nrx, gen ^ tb, gen ^ bb] []
      (l4Pops D j ++ pt) := by
  have hs := D.slot_lt j hj
  set s := D.slot j with hsd
  set σ := l4σ rd j nrs Y cv X nrx tb bb s with hσ
  have hw := Main.walk_straight σ [] l4Pre l4Pre_straight
  rw [← l4_body] at hw
  obtain ⟨hpd, hpa, hpad, hpc⟩ := Main.straight_parts σ _ l4Pre_straight
  set es := l4Pre.flatMap (Main.slEvs σ) with hes
  have hal : allocs σ es = [] := by rw [hpa]; rfl
  have htk : decide (σ (.n 20) ≠ 0) = decide (j + 1 < nrs) := by
    show decide (gen ^ j * word 2 0 + gen ^ nrs ≠ 0) = _
    rw [guard_taken hnrs (by omega)]
    exact decide_eq_decide.mpr (by omega)
  have hcalls : calls es = [⟨"verify_sig_lean_sphincs", [.n 17, .n 6], [], true⟩] ++
      [⟨name% «main_loop3», [.n 22, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6], [], decide (j + 1 < nrs)⟩] := by
    rw [hpc, show l4Pre.filterMap Main.Stmt.callS =
      [(none, "verify_sig_lean_sphincs", [.n 17, .n 6], []),
      (some (.n 20), name% «main_loop3», [.n 22, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6], [])] from rfl]
    simp only [List.map_cons, List.map_nil, Main.mkCall, htk, List.cons_append, List.nil_append]
  have hev : ∀ e ∈ es, e.Holds rd σ := by
    refine slEvs_holds fun st hst => ?_
    simp only [l4Pre, List.mem_cons, List.not_mem_nil, or_false] at hst
    rcases hst with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl
    all_goals simp only [SlOk, Atom.Holds, hσ, l4σ, ofArgs_n, List.getD_cons_succ, List.getD_cons_zero]
    · refine ⟨low_read hl (by omega), ?_, low_read hl (by omega)⟩
      rw [gen_pow_mul_ginv (by omega), ← pow_add]; congr 1; omega
    · rw [show gen ^ (cv + X) * gen ^ s = gen ^ cv * gen ^ (X + s) by
          rw [← pow_add, ← pow_add, Nat.add_assoc],
        show gen ^ nrx * gen ^ j = gen ^ (nrx + j) by rw [← pow_add], loadHolds_mul_gen_pow, Nat.add_zero]
      exact D.cover rd hl hL j hj
    · rw [word_gen, gen_pow_mul_gen]; exact gen_pow_add_isInK _ _
  -- the pops
  have hps : splice rd σ es ([Sig.spSegPops (D.pk j) (D.msg j) (D.sig j)] ++ [pt]) = l4Pops D j ++ pt := by
    have hx : SplicePops rd σ l4Pre ([] ++ [Sig.spSegPops (D.pk j) (D.msg j) (D.sig j)] ++ [] ++ [pt])
        (Sig.atomsPops rd σ l4A ++ Sig.spSegPops (D.pk j) (D.msg j) (D.sig j) ++ Sig.atomsPops rd σ l4B ++ pt) := by
      rw [l4Pre_split]
      exact (((SplicePops.of_fallPops (Sig.fallPops_atoms σ l4A_atoms)).append (SplicePops.call _ _ _ _)).append
        (SplicePops.of_fallPops (Sig.fallPops_atoms σ l4B_atoms))).append (splicePops_callIf _ _ _ _)
    rw [show ([] ++ [Sig.spSegPops (D.pk j) (D.msg j) (D.sig j)] ++ [] ++ [pt] : List (List Pop)) =
      [Sig.spSegPops (D.pk j) (D.msg j) (D.sig j)] ++ [pt] from rfl] at hx
    rw [splice_of_body l4_body hx (show walk σ [.ret []] = .ret [] [] by simp [walk, walk1, Out.seq]) rfl hw,
      l4A_pops, l4B_pops]
    simp only [evPops, List.flatMap_nil, List.append_nil]
    rfl
  -- the call of the check
  have hv := hV rd (RegionL Lin) (gen ^ (tb + 4 * s)) (gen ^ bb) (D.pk j) (D.msg j) (D.sig j)
    (fun i hi => hl i (by omega)) (D.bytes rd hl hL) (D.claim rd hl hL j hj) (D.verify j hj)
    (fun k hk => ⟨tb + 4 * s + k, limb0_gen_pow_mul _ _, D.regClaim j hj k hk⟩)
    (fun v hv => ⟨bb + v, limb0_gen_pow_mul _ _, D.regBytes v hv⟩) (c + 0)
  have hva : ([.n 17, .n 6] : List V).map σ = [gen ^ (tb + 4 * s), gen ^ bb] := by
    show [gen ^ tb * (gen ^ s * gen ^ s * (gen ^ s * gen ^ s)), gen ^ bb] = _
    rw [gen4, ← pow_add]
  have h := relAtInPE_of_walk_loop (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd) (Q := Q rd)
    coreProgram_wf (R := RegionL Lin) (D := RegionL []) (Dk := fun _ => False) (Rt := RegionL Lin)
    (Dt := RegionL []) (fp := fp) (c := c) (Bt := Bt) (m := m) (N := nV)
    (pss := [Sig.spSegPops (D.pk j) (D.msg j) (D.sig j)]) (pt := pt)
    l4_find main_loop3_loop (by rw [l4_params]) hw rfl hev hcalls ?_
    (by rw [hpd, hal, show l4Pre.filterMap Main.Stmt.allocSz = [] from rfl]; rfl)
    (fun q hq => by rw [hpad, show l4Pre.filterMap Main.Stmt.addrS = [] from rfl] at hq; simp at hq)
    ⟨nV, 0, RegionL Lin, fun _ => False, (Nat.add_zero nV).symm, fun i hi => Or.inl (Or.inl hi),
      by rw [ite_eq_left_of_eq_true _ _ (eq_true rfl), hva, hal]; exact hv, rfl, fun _ h => h.elim⟩
    (fun i hi => Or.inl hi) ?_ (fun i hi => by simp [RegionL] at hi) hps (hq σ _ _ hw hev)
  · simp only [hal, List.sum_nil, Nat.zero_add] at h; exact h
  · rw [hal, List.sum_nil, Nat.add_zero]
    have hta : ([.n 22, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6] : List V).map σ =
        [gen ^ (j + 1), gen ^ nrs, gen ^ Y, gen ^ (cv + X), gen ^ nrx, gen ^ tb, gen ^ bb] := by
      show [gen ^ j * word 2 0, gen ^ nrs, gen ^ Y, gen ^ (cv + X), gen ^ nrx, gen ^ tb, gen ^ bb] = _
      rw [word_gen, gen_pow_mul_gen]
    by_cases hn : j + 1 < nrs
    · simp only [hn, ↓reduceIte] at htail
      simp only [hn, decide_true, ↓reduceIte, List.map_nil, hta]
      exact htail
    · simp only [hn, ↓reduceIte] at htail
      simp only [hn, decide_false, Bool.false_eq_true, ↓reduceIte]
      exact htail
  · intro A hA
    rw [B1.loadAddrs_straight σ _ l4Pre_straight,
      show l4Pre.filterMap B1.Stmt.loadS = [(.n 14, 0)] from rfl] at hA
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hA
    subst hA
    refine ⟨cv + (X + s), ?_, Or.inr (Or.inl (D.regCover j hj))⟩
    show (gen ^ (cv + X) * gen ^ s).limb 0 * addressOfIndex 0 = _
    rw [← pow_add, Nat.add_assoc, limb0_gen_pow_mul]; rfl

/-- **`main_loop3` from the counter `g^j`, placed, with its pops, every node satisfying `Q`**: iterations
`j ..< nrs`' entries in order. -/
theorem rawS_loopPQ (fs : String → ℕ) (cert : String → V → ℕ) {nV : ℕ} {Q : Reader → String → Val → Prop}
    (hV : VerifySigPQ fs cert nV Q)
    {nrs Y X nrx cv tb bb : ℕ} {Lin : Layout} (D : RawSData nrs Y X nrx cv tb bb Lin) (hY : Y ≤ 2 ^ 23)
    (hnrs : nrs < 2 ^ 34) {rd : Reader} (hl : LowDef 23 rd) (hL : MemL rd Lin)
    (hq : ∀ σ es vs, walk σ (coreProgram.getD idx% «main_loop3» default).body = .ret es vs →
      (∀ e ∈ es, e.Holds rd σ) → Q rd name% «main_loop3» σ) :
    ∀ j < nrs, ∀ fp c, RelAtInCPE coreProgram fs cert rd (Q rd) (RegionL Lin) (RegionL []) fp c
      ((nrs - j + 1) * fs name% «main_loop3») ((nrs - j) * nV) name% «main_loop3»
      [gen ^ j, gen ^ nrs, gen ^ Y, gen ^ (cv + X), gen ^ nrx, gen ^ tb, gen ^ bb] []
      ((List.range' j (nrs - j)).flatMap (l4Pops D)) := by
  suffices key : ∀ t j, j + 1 + t = nrs → ∀ fp c, RelAtInCPE coreProgram fs cert rd (Q rd) (RegionL Lin) (RegionL [])
      fp c
      ((nrs - j + 1) * fs name% «main_loop3») ((nrs - j) * nV) name% «main_loop3»
      [gen ^ j, gen ^ nrs, gen ^ Y, gen ^ (cv + X), gen ^ nrx, gen ^ tb, gen ^ bb] []
      ((List.range' j (nrs - j)).flatMap (l4Pops D)) from
    fun j hj => key (nrs - j - 1) j (by omega)
  intro t
  induction t with
  | zero =>
    intro j hj fp c
    have h := rawS_stepPQ fs cert hV D hY hnrs hl hL hq (j := j) (fp := fp) (c := c) (Bt := fs name% «main_loop3»)
      (m := 0) (pt := []) (by omega) (by rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]; exact ⟨rfl, rfl, rfl⟩)
    rw [show nrs - j = 1 by omega, List.range'_one, List.flatMap_singleton, show (1 + 1) * fs name% «main_loop3» =
      fs name% «main_loop3» + fs name% «main_loop3» by ring, Nat.one_mul]
    rw [List.append_nil, Nat.add_zero] at h
    exact h
  | succ t ih =>
    intro j hj fp c
    have h := rawS_stepPQ fs cert hV D hY hnrs hl hL hq (j := j) (fp := fp) (c := c) (by omega)
      (by rw [ite_eq_left_of_eq_true _ _ (eq_true (by omega))]
          exact ih (j + 1) (by omega) (fp + fs name% «main_loop3») (c + nV))
    rw [show nrs - j = nrs - (j + 1) + 1 by omega, List.range'_succ, List.flatMap_cons,
      show (nrs - (j + 1) + 1 + 1) * fs name% «main_loop3» =
        fs name% «main_loop3» + (nrs - (j + 1) + 1) * fs name% «main_loop3» by ring,
      show (nrs - (j + 1) + 1) * nV = nV + (nrs - (j + 1)) * nV by ring]
    exact h

theorem rawS_stepP (fs : String → ℕ) (cert : String → V → ℕ) {nV : ℕ} (hV : VerifySigP fs cert nV)
    {nrs Y X nrx cv tb bb : ℕ} {Lin : Layout} (D : RawSData nrs Y X nrx cv tb bb Lin) (hY : Y ≤ 2 ^ 23)
    (hnrs : nrs < 2 ^ 34) {rd : Reader} (hl : LowDef 23 rd) (hL : MemL rd Lin) {j : ℕ} (hj : j < nrs)
    {fp c Bt m : ℕ} {pt : List Pop}
    (htail : if j + 1 < nrs then
        RelAtInCP coreProgram fs cert rd (RegionL Lin) (RegionL []) (fp + fs name% «main_loop3») (c + nV) Bt m
          name% «main_loop3» [gen ^ (j + 1), gen ^ nrs, gen ^ Y, gen ^ (cv + X), gen ^ nrx, gen ^ tb, gen ^ bb] [] pt
      else Bt = fs name% «main_loop3» ∧ m = 0 ∧ pt = []) :
    RelAtInCP coreProgram fs cert rd (RegionL Lin) (RegionL []) fp c (fs name% «main_loop3» + Bt) (nV + m)
      name% «main_loop3» [gen ^ j, gen ^ nrs, gen ^ Y, gen ^ (cv + X), gen ^ nrx, gen ^ tb, gen ^ bb] []
      (l4Pops D j ++ pt) := by
  refine (rawS_stepPQ fs cert hV.toPQ D hY hnrs hl hL (fun _ _ _ _ _ => trivial) hj ?_).toP
  by_cases hn : j + 1 < nrs
  · rw [ite_eq_left_of_eq_true _ _ (eq_true hn)] at htail ⊢
    exact htail.withEvery fun t _ _ => Tree.every_true t
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hn)] at htail ⊢
    exact htail

theorem rawS_loopP (fs : String → ℕ) (cert : String → V → ℕ) {nV : ℕ} (hV : VerifySigP fs cert nV)
    {nrs Y X nrx cv tb bb : ℕ} {Lin : Layout} (D : RawSData nrs Y X nrx cv tb bb Lin) (hY : Y ≤ 2 ^ 23)
    (hnrs : nrs < 2 ^ 34) {rd : Reader} (hl : LowDef 23 rd) (hL : MemL rd Lin) :
    ∀ j < nrs, ∀ fp c, RelAtInCP coreProgram fs cert rd (RegionL Lin) (RegionL []) fp c
      ((nrs - j + 1) * fs name% «main_loop3») ((nrs - j) * nV) name% «main_loop3»
      [gen ^ j, gen ^ nrs, gen ^ Y, gen ^ (cv + X), gen ^ nrx, gen ^ tb, gen ^ bb] []
      ((List.range' j (nrs - j)).flatMap (l4Pops D)) := fun j hj fp c =>
  (rawS_loopPQ fs cert hV.toPQ D hY hnrs hl hL (fun _ _ _ _ _ => trivial) j hj fp c).toP

/-- **`main_loop3` is complete, placed, with its pops, every node satisfying `Q`**, from every counter `g^j` below
the count: iterations `j ..< nrs`' entries in order. -/
theorem rawS_completeAtDPQ (fs : String → ℕ) (cert : String → V → ℕ) {nV : ℕ} {Q : Reader → String → Val → Prop}
    (hV : VerifySigPQ fs cert nV Q)
    {nrs Y X nrx cv tb bb : ℕ} {Lin : Layout} (D : RawSData nrs Y X nrx cv tb bb Lin) (hY : Y ≤ 2 ^ 23)
    (hnrs : nrs < 2 ^ 34)
    (hq : ∀ rd σ es vs, walk σ (coreProgram.getD idx% «main_loop3» default).body = .ret es vs →
      (∀ e ∈ es, e.Holds rd σ) → Q rd name% «main_loop3» σ) :
    ∀ j < nrs, CompleteAtDPE fs cert 23 name% «main_loop3» Lin
      [gen ^ j, gen ^ nrs, gen ^ Y, gen ^ (cv + X), gen ^ nrx, gen ^ tb, gen ^ bb] (Returns [])
      (fun _ => (List.range' j (nrs - j)).flatMap (l4Pops D)) Q := fun j hj fp =>
  ⟨(nrs - j + 1) * fs name% «main_loop3» + (nrs - j) * nV, [], [], [], ⟨rfl, rfl⟩, by simp [Within], disj_nil,
    fun rd hl hL => (rawS_loopPQ fs cert hV D hY hnrs hl (by simpa using hL) (hq rd) j hj fp
      (fp + (nrs - j + 1) * fs name% «main_loop3»)).relAtInPE⟩

/-- **`main_loop3` is complete, placed, with its pops**, from every counter `g^j` below the count: iterations
`j ..< nrs`' entries in order. -/
theorem rawS_completeAtDP (fs : String → ℕ) (cert : String → V → ℕ) {nV : ℕ} (hV : VerifySigP fs cert nV)
    {nrs Y X nrx cv tb bb : ℕ} {Lin : Layout} (D : RawSData nrs Y X nrx cv tb bb Lin) (hY : Y ≤ 2 ^ 23)
    (hnrs : nrs < 2 ^ 34) :
    ∀ j < nrs, CompleteAtDP fs cert 23 name% «main_loop3» Lin
      [gen ^ j, gen ^ nrs, gen ^ Y, gen ^ (cv + X), gen ^ nrx, gen ^ tb, gen ^ bb] (Returns [])
      (fun _ => (List.range' j (nrs - j)).flatMap (l4Pops D)) := fun j hj =>
  (rawS_completeAtDPQ fs cert hV.toPQ D hY hnrs (fun _ _ _ _ _ _ => trivial) j hj).toDP

end
end LeanVM.Guest.B1.Main
