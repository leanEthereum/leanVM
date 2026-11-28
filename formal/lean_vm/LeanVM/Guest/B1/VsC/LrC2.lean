/-
  LeanVM.Guest.B1.VsC.LrC2

  `level_residual`'s rest's loop completes with no words of its own, and every valid tree of it
  has its shape.
-/

module

public import LeanVM.Guest.B1.VsC.LrC

/-!
# `level_residual`'s rest's loop, complete

After the `b` batches, `level_residual` runs `r = q % resBatch` single steps from the chain pair `b`
(`rest = chain·g^(2b)`) over the positions from `resBatch·b` (`tail = positions·g^(resBatch·b)`).
`lr2_loop`, `lr2_shape` as `lr1_loop`, `lr1_shape` (`LrC.lean`).
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.Value LeanVM.Guest.B1.Whir
open LeanVM.Protocol.Verifier

@[expose] public section

theorem lrCnt_rest (b j : ℕ) : lrCnt b (b + j) = resBatch * b + j := by
  unfold lrCnt
  split_ifs with h
  · have : j = 0 := by omega
    subst this; simp
  · omega

theorem lrPair_succ (P H : E → E) (mu : E) (Pos : ℕ → E) (n : ℕ) :
    lrPair P H mu Pos (n + 1) =
      (((lrPair P H mu Pos n).1 + P (Pos n)) * mu, ((lrPair P H mu Pos n).2 + H (Pos n)) * mu) := by
  rw [← lrPair_add]
  simp [resFold]

/-- The rest's loop's stores: the next pair into the step's chain cells `2`, `3`. -/
def lr2Stores (cols nhs hbits : ℕ) : List Atom :=
  [.load (.n ((lr2Q cols nhs hbits).2.2.2 + 2)) (.n 8) 2, .load (.n ((lr2Q cols nhs hbits).2.2.2 + 5)) (.n 8) 3]

/-- The rest's loop's pointers: the row, the high part, the step's position, its chain pair. -/
def lr2Ps (cols nhs : ℕ) : List (ℕ × ℕ) := [(4, cols), (5, nhs), (9, 1), (8, 4)]

abbrev lr2L (cols nhs hbits : ℕ) : List Stmt := lr2A cols nhs hbits ++ osLoopTailA ((lr2Q cols nhs hbits).2.2.2 + 6)

abbrev lr2T (cols nhs hbits : ℕ) : List V :=
  .n ((lr2Q cols nhs hbits).2.2.2 + 6 + 4) :: (List.range (7 - 1)).map fun i ↦ .n (i + 1)

/-- What the kernel checks of a specialization's rest's loop. -/
def lr2Checks (cols nhs hbits : ℕ) (name : String) : Bool :=
  (chk 7 (lrLoop2Body cols nhs hbits name)).isSome &&
    decide (storesOf 7 (lrLoop2Body cols nhs hbits name) = lr2Stores cols nhs hbits) &&
    (lr2L cols nhs hbits).all Stmt.isAtom &&
    (atomsOf (lr2L cols nhs hbits)).all (loadOkB (lr2Ps cols nhs)) &&
    (lr2Q cols nhs hbits).1.all Stmt.isAtom &&
    (atomsOf (lr2Q cols nhs hbits).1).all (fun a => decide (a ∉ lr2Stores cols nhs hbits)) &&
    decide (1 ≤ cols ∧ 1 ≤ nhs ∧ hbits ≤ 3 ∧ hbits ≤ cols + 1 ∧ 6 < (lr2Q cols nhs hbits).2.2.2)

/-- The rest's loop's arguments at step `j` of `r`. -/
def lr2Args (j r irs itl irow ihs : ℕ) (mu : E) : List E :=
  [gen ^ j, gen ^ r, ptrAt irs, ptrAt itl, ptrAt irow, ptrAt ihs, mu]

theorem lr2_body {cols nhs hbits : ℕ} {name : String} (hat : (lr2L cols nhs hbits).all Stmt.isAtom = true) :
    lrLoop2Body cols nhs hbits name = ((atomsOf (lr2L cols nhs hbits)).map Stmt.atom ++
      [Stmt.callIf (.n ((lr2Q cols nhs hbits).2.2.2 + 6 + 2)) name (lr2T cols nhs hbits)]) ++ [.ret []] := by
  rw [lrLoop2Body_split, ← eq_map_atomsOf (allAtoms_of_isAtom hat)]
  simp [List.append_assoc]

theorem mem_lr2L_q {cols nhs hbits : ℕ} {s : Stmt} (h : s ∈ (lr2Q cols nhs hbits).1) : s ∈ lr2L cols nhs hbits := by
  simp [lr2L, lr2A, h]

theorem mem_lr2L_tail {cols nhs hbits : ℕ} {s : Stmt} (h : s ∈ osLoopTailA ((lr2Q cols nhs hbits).2.2.2 + 6)) :
    s ∈ lr2L cols nhs hbits := by
  simp [lr2L, h]

/-- **The rest's loop's pointers and guard.** -/
theorem lr2_vals {cols nhs hbits : ℕ} {rd : Reader} {σ : Val} {j r irs itl irow ihs : ℕ} {mu : E}
    (hp : ∀ i < 7, σ (.n i) = (lr2Args j r irs itl irow ihs mu).getD i 0)
    (hNS : ∀ a, Stmt.atom a ∈ lr2L cols nhs hbits → needsSide a = false → a.Holds rd σ) :
    σ (.n 9) = ptrAt (itl + j) ∧ σ (.n 8) = ptrAt (irs + 2 * j) ∧
      σ (.n 4) = ptrAt irow ∧ σ (.n 5) = ptrAt ihs ∧ σ (.n 6) = mu ∧
      σ (.n ((lr2Q cols nhs hbits).2.2.2 + 6 + 2)) = gen ^ (j + 1) + gen ^ r ∧
      (lr2T cols nhs hbits).map σ = lr2Args (j + 1) r irs itl irow ihs mu := by
  have p0 : σ (.n 0) = gen ^ j := hp 0 (by decide)
  have p1 : σ (.n 1) = gen ^ r := hp 1 (by decide)
  have p2 : σ (.n 2) = ptrAt irs := hp 2 (by decide)
  have p3 : σ (.n 3) = ptrAt itl := hp 3 (by decide)
  have p4 : σ (.n 4) = ptrAt irow := hp 4 (by decide)
  have p5 : σ (.n 5) = ptrAt ihs := hp 5 (by decide)
  have p6 : σ (.n 6) = mu := hp 6 (by decide)
  have e7 : σ (.n 7) = σ (.n 2) * σ (.n 0) := hNS (.mul (.n 7) (.n 2) (.n 0)) (by simp [lr2L, lr2A]) (by decide)
  have e8 : σ (.n 8) = σ (.n 7) * σ (.n 0) := hNS (.mul (.n 8) (.n 7) (.n 0)) (by simp [lr2L, lr2A]) (by decide)
  have e9 : σ (.n 9) = σ (.n 3) * σ (.n 0) := hNS (.mul (.n 9) (.n 3) (.n 0)) (by simp [lr2L, lr2A]) (by decide)
  have hT : AllOk (fun _ _ _ => True) rd σ (osLoopTailA ((lr2Q cols nhs hbits).2.2.2 + 6)) :=
    allOk_noSide (fun _ h => mem_lr2L_tail h) (osLoopTailA_noSide _) hNS
  obtain ⟨t2, t4⟩ := osLoopTailA_val hT
  refine ⟨?_, ?_, p4, p5, p6, ?_, ?_⟩
  · rw [e9, p3, p0, ptrAt_mul_gen]
  · rw [e8, e7, p2, p0, ptrAt_mul_gen, ptrAt_mul_gen, show irs + j + j = irs + 2 * j by omega]
  · rw [t2, p0, p1, ← pow_succ]
  · show [σ (.n ((lr2Q cols nhs hbits).2.2.2 + 6 + 4)), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5),
      σ (.n 6)] = _
    rw [t4, p0, p1, p2, p3, p4, p5, p6, ← pow_succ]
    rfl

/-- **One step of the rest's loop completes**, the next one completing when `j + 1 < r`. -/
theorem lr2_step {kd : ℕ} {cols nhs hbits : ℕ} {name : String} {fn : Fn}
    (hfind : coreProgram.find? name = some fn) (hpar : fn.params = osParams 7)
    (hbody : fn.body = lrLoop2Body cols nhs hbits name) (hck : lr2Checks cols nhs hbits name = true)
    {q : ℕ} (_hq : q < 2 ^ 30) (ip irow ihs ic : ℕ) (mu : E) (D Pos : ℕ → E) (hsv : List E)
    (hlen : hsv.length = nhs) {j : ℕ} (hj : j < q % resBatch)
    (hnext : j + 1 < q % resBatch → CallCompletes0 kd name
      (lr2Args (j + 1) (q % resBatch) (ic + 2 * (q / resBatch)) (ip + resBatch * (q / resBatch)) irow ihs mu) []
      (LrMem q cols nhs hbits ip irow ihs ic mu D Pos hsv) PostQuiet) :
    CallCompletes0 kd name
      (lr2Args j (q % resBatch) (ic + 2 * (q / resBatch)) (ip + resBatch * (q / resBatch)) irow ihs mu) []
      (LrMem q cols nhs hbits ip irow ihs ic mu D Pos hsv) PostQuiet := by
  simp only [lr2Checks, Bool.and_eq_true, decide_eq_true_eq] at hck
  obtain ⟨⟨⟨⟨⟨⟨hc, hst⟩, hat⟩, hok⟩, hat1⟩, hns⟩, hc1, hn1, hb3, hbn, he6⟩ := hck
  obtain ⟨c', hc⟩ := Option.isSome_iff_exists.mp hc
  set b := q / resBatch with hb
  set r := q % resBatch with hr
  have hqbr : resBatch * b + r = q := Nat.div_add_mod q resBatch
  have hr8 : r < resBatch := Nat.mod_lt _ (by decide)
  set args := lr2Args j r (ic + 2 * b) (ip + resBatch * b) irow ihs mu with hargs
  have hb' := lr2_body (name := name) hat
  have hchk : chk args.length fn.body = some c' := by rw [hbody]; exact hc
  refine callCompletes0_loopFlat hfind (by rw [hbody]; exact hb') (by rw [hpar]; rfl) hok
    (fun rd => fwdVal rd (fun _ => 0) args fn.body) fun rd hl hP => ?_
  set s := fwdVal rd (fun _ => 0) args fn.body with hs
  have hmem : ∀ a, Stmt.atom a ∈ lr2L cols nhs hbits → Stmt.atom a ∈ fn.body := fun a ha => by
    rw [hbody, hb']
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨a, mem_atomsOf' ha, rfl⟩))
  have hNS : ∀ a, Stmt.atom a ∈ lr2L cols nhs hbits → needsSide a = false → a.Holds rd s :=
    fun a ha hn => fwd_holds_noSide hchk (hmem a ha) hn
  have hp : ∀ i < 7, s (.n i) = args.getD i 0 := fun i hi => fwd_param hchk (by simpa [hargs, lr2Args] using hi)
  obtain ⟨v9, v8, p4, p5, p6, vg, vt⟩ := lr2_vals hp hNS
  have hbase : ∀ q' ∈ lr2Ps cols nhs, ∃ a, s (.n q'.1) = ptrAt a ∧
      ∀ o < q'.2, ∃ v, LoadHolds rd (ptrAt a) o v := by
    intro q' hq'
    simp only [lr2Ps, List.mem_cons, List.not_mem_nil, or_false] at hq'
    rcases hq' with rfl | rfl | rfl | rfl
    · exact ⟨irow, p4, fun o ho => ⟨_, lrMem_row hP ho⟩⟩
    · exact ⟨ihs, p5, fun o ho => ⟨_, lrMem_high hP (by omega)⟩⟩
    · exact ⟨ip + resBatch * b + j, v9, fun o ho => ⟨_, by
        rw [Nat.add_assoc]; exact lrMem_pos hP (by simp only at ho; omega)⟩⟩
    · exact ⟨ic + 2 * b + 2 * j, v8, fun o ho => ⟨_, by
        rw [Nat.add_assoc]; exact readsAt_off hP.2.2.2 (by simp only at ho; simp [lrChainL]; omega)⟩⟩
  have hP1 : ∀ a, Stmt.atom a ∈ lr2L cols nhs hbits → a ∉ lr2Stores cols nhs hbits → a.Holds rd s := by
    intro a ha hS
    cases hn : needsSide a
    · exact hNS a ha hn
    · have hk := List.all_eq_true.mp hok a (mem_atomsOf' ha)
      cases a with
      | load d p off =>
        refine fwd_holds_load hchk (hmem _ ha) ?_ (loadHolds_of_loadOk hbase hk)
        show Atom.load d p off ∉ storesOf 7 fn.body
        rw [hbody, hst]; exact hS
      | _ => simp [loadOkB, hn] at hk
  set e := (lr2Q cols nhs hbits).2.2.2 with he
  have he6' : 6 < e := he6
  -- the position and the chain pair it reads
  have l10 : LoadHolds rd (s (.n 9)) 0 (s (.n 10)) :=
    hP1 (.load (.n 10) (.n 9) 0) (by simp [lr2L, lr2A]) (by simp [lr2Stores])
  have le : LoadHolds rd (s (.n 8)) 0 (s (.n e)) :=
    hP1 (.load (.n e) (.n 8) 0) (by simp [lr2L, lr2A, he]) (by simp [lr2Stores])
  have le3 : LoadHolds rd (s (.n 8)) 1 (s (.n (e + 3))) :=
    hP1 (.load (.n (e + 3)) (.n 8) 1) (by simp [lr2L, lr2A, he]) (by simp [lr2Stores])
  rw [v9, Nat.add_assoc, loadHolds_ptrAt_add, Nat.add_zero] at l10
  rw [v8, Nat.add_assoc, loadHolds_ptrAt_add, Nat.add_zero] at le
  rw [v8, Nat.add_assoc, loadHolds_ptrAt_add] at le3
  have x10 : s (.n 10) = Pos (resBatch * b + j) := loadHolds_unique l10 (by
    have := lrMem_pos hP (m := resBatch * b + j) (o := 0) (by omega)
    rw [loadHolds_ptrAt_add, Nat.add_zero] at this; exact this)
  obtain ⟨c0, c1⟩ := lrChain_load hP.2.2.2 (i := b + j) (by omega)
  have xe : s (.n e) = (lrPair (lrP cols D) (lrH cols nhs hbits hsv) mu Pos (lrCnt b (b + j))).1 :=
    loadHolds_unique le (by rw [show 2 * b + 2 * j = 2 * (b + j) by ring]; exact c0)
  have xe3 : s (.n (e + 3)) = (lrPair (lrP cols D) (lrH cols nhs hbits hsv) mu Pos (lrCnt b (b + j))).2 :=
    loadHolds_unique le3 (by rw [show 2 * b + 2 * j + 1 = 2 * (b + j) + 1 by ring]; exact c1)
  -- the query
  have hq1 : AllOk (fun _ _ _ => True) rd s (osResQuery 10 4 0 5 0 (lrVo cols) cols nhs hbits 11).1 := by
    intro st hst'
    have h1 := List.all_eq_true.mp hat1 st hst'
    cases st with
    | atom a =>
      refine hP1 a (mem_lr2L_q hst') ?_
      have := List.all_eq_true.mp hns a (mem_atomsOf' hst')
      simpa using this
    | _ => simp [Stmt.isAtom] at h1
  have hDs : ∀ t < cols, LoadHolds rd (s (.n 4)) (0 + t) (D t) := fun t ht => by
    rw [p4, Nat.zero_add]; exact lrMem_row hP ht
  have hHs : ∀ c < nhs, LoadHolds rd (s (.n 5)) (0 + c) (hsv.getD c 0) := fun c hc => by
    rw [p5, Nat.zero_add]; exact lrMem_high hP (by omega)
  obtain ⟨q1, q2⟩ := osResQuery_val hc1 hn1 hb3 hbn hDs hlen hHs hq1
  have q1' : s (.n (lr2Q cols nhs hbits).2.1) = residualProd (osVals (lrVo cols) cols) (s (.n 10)) D cols := q1
  have q2' : s (.n (lr2Q cols nhs hbits).2.2.1) = residualChain (osVals (lrVo cols) cols) (s (.n 10)) cols *
      novelSum hsv (residualChain (osVals (lrVo cols) cols) (s (.n 10))) nhs hbits := q2
  have a1 : s (.n (e + 1)) = s (.n e) + s (.n (lr2Q cols nhs hbits).2.1) :=
    hNS (.add (.n (e + 1)) (.n e) (.n (lr2Q cols nhs hbits).2.1)) (by simp [lr2L, lr2A, he]) (by simp [needsSide])
  have m2 : s (.n (e + 2)) = s (.n (e + 1)) * s (.n 6) :=
    hNS (.mul (.n (e + 2)) (.n (e + 1)) (.n 6)) (by simp [lr2L, lr2A, he]) (by simp [needsSide]; omega)
  have a4 : s (.n (e + 4)) = s (.n (e + 3)) + s (.n (lr2Q cols nhs hbits).2.2.1) :=
    hNS (.add (.n (e + 4)) (.n (e + 3)) (.n (lr2Q cols nhs hbits).2.2.1)) (by simp [lr2L, lr2A, he]) (by simp [needsSide])
  have m5 : s (.n (e + 5)) = s (.n (e + 4)) * s (.n 6) :=
    hNS (.mul (.n (e + 5)) (.n (e + 4)) (.n 6)) (by simp [lr2L, lr2A, he]) (by simp [needsSide]; omega)
  have hcj1 : lrCnt b (b + j + 1) = lrCnt b (b + j) + 1 := by
    rw [show b + j + 1 = b + (j + 1) by ring, lrCnt_rest, lrCnt_rest]; ring
  obtain ⟨d0, d1⟩ := lrChain_load hP.2.2.2 (i := b + j + 1) (by omega)
  rw [hcj1, lrPair_succ, lrCnt_rest] at d0 d1
  have hS1 : LoadHolds rd (s (.n 8)) 2 (s (.n (e + 2))) := by
    have h1 : s (.n (e + 2)) = ((lrPair (lrP cols D) (lrH cols nhs hbits hsv) mu Pos (resBatch * b + j)).1 +
        lrP cols D (Pos (resBatch * b + j))) * mu := by
      rw [m2, a1, xe, p6, q1', x10, lrCnt_rest]; rfl
    rw [v8, Nat.add_assoc, loadHolds_ptrAt_add, h1, show 2 * b + 2 * j + 2 = 2 * (b + j + 1) by ring]
    exact d0
  have hS2 : LoadHolds rd (s (.n 8)) 3 (s (.n (e + 5))) := by
    have h1 : s (.n (e + 5)) = ((lrPair (lrP cols D) (lrH cols nhs hbits hsv) mu Pos (resBatch * b + j)).2 +
        lrH cols nhs hbits hsv (Pos (resBatch * b + j))) * mu := by
      rw [m5, a4, xe3, p6, q2', x10, lrCnt_rest]; rfl
    rw [v8, Nat.add_assoc, loadHolds_ptrAt_add, h1, show 2 * b + 2 * j + 3 = 2 * (b + j + 1) + 1 by ring]
    exact d1
  refine ⟨by rw [hpar]; exact fwd_params hchk, fun a ha => ?_, ?_, fun hz => ?_⟩
  · have ha' := mem_of_mem_atomsOf ha
    by_cases hS : a ∈ lr2Stores cols nhs hbits
    · simp only [lr2Stores, List.mem_cons, List.not_mem_nil, or_false] at hS
      rcases hS with rfl | rfl
      · exact hS1
      · exact hS2
    · exact hP1 a ha' hS
  · rw [vg]; exact isInK_add (gen_pow_isInK _) (gen_pow_isInK _)
  · have hne : j + 1 ≠ r := fun h => hz (by rw [vg, h]; exact CharTwo.add_self_eq_zero _)
    obtain ⟨t, hn, hv2, hb2, hq2⟩ := hnext (by omega) rd hl hP
    exact ⟨t, hn, by rw [vt]; exact hv2, hb2, hq2⟩

/-- **The rest's loop completes from step `j`**, every `j < r`. -/
theorem lr2_loop {kd : ℕ} {cols nhs hbits : ℕ} {name : String} {fn : Fn}
    (hfind : coreProgram.find? name = some fn) (hpar : fn.params = osParams 7)
    (hbody : fn.body = lrLoop2Body cols nhs hbits name) (hck : lr2Checks cols nhs hbits name = true)
    {q : ℕ} (hq : q < 2 ^ 30) (ip irow ihs ic : ℕ) (mu : E) (D Pos : ℕ → E) (hsv : List E)
    (hlen : hsv.length = nhs) :
    ∀ m j, q % resBatch = j + m + 1 → CallCompletes0 kd name
      (lr2Args j (q % resBatch) (ic + 2 * (q / resBatch)) (ip + resBatch * (q / resBatch)) irow ihs mu) []
      (LrMem q cols nhs hbits ip irow ihs ic mu D Pos hsv) PostQuiet := by
  intro m
  induction m with
  | zero =>
    intro j hj
    exact lr2_step hfind hpar hbody hck hq ip irow ihs ic mu D Pos hsv hlen (by omega)
      (fun h => absurd h (by omega))
  | succ m IH =>
    intro j hj
    exact lr2_step hfind hpar hbody hck hq ip irow ihs ic mu D Pos hsv hlen (by omega)
      (fun _ => IH (j + 1) (by omega))

/-- **Every valid tree of the rest's loop from step `j < r` has its shape.** -/
theorem lr2_shape {fs : String → ℕ} {al : String → Bool} {cols nhs hbits : ℕ} {name : String} {fn : Fn}
    (hfind : coreProgram.find? name = some fn) (hpar : fn.params = osParams 7)
    (hbody : fn.body = lrLoop2Body cols nhs hbits name) (hls : coreProgram.loop name = true)
    (hck : lr2Checks cols nhs hbits name = true) {q : ℕ} {ip irow ihs ic : ℕ} {mu : E}
    {R : ℕ → Prop} (hR : LrRegion q cols nhs ip irow ihs ic R) :
    ∀ m j, q % resBatch = j + m + 1 → ∀ rd t, t.name = name →
      t.Valid coreProgram rd
        (lr2Args j (q % resBatch) (ic + 2 * (q / resBatch)) (ip + resBatch * (q / resBatch)) irow ihs mu) [] →
      t.BufsOk coreProgram → ShapeR fs al (lpB fs name (q % resBatch) j) _root_.id R t := by
  simp only [lr2Checks, Bool.and_eq_true, decide_eq_true_eq] at hck
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hat⟩, hok⟩, -⟩, -⟩, -⟩ := hck
  have hb' := lr2_body (name := name) hat
  set b := q / resBatch with hb
  set r := q % resBatch with hr
  have hqbr : resBatch * b + r = q := Nat.div_add_mod q resBatch
  have hr8 : r < resBatch := Nat.mod_lt _ (by decide)
  have h8 : resBatch = 8 := rfl
  have hbase : ∀ (σ : Val) (j : ℕ), j < r → σ (.n 9) = ptrAt (ip + resBatch * b + j) →
      σ (.n 8) = ptrAt (ic + 2 * b + 2 * j) → σ (.n 4) = ptrAt irow → σ (.n 5) = ptrAt ihs →
      ∀ q' ∈ lr2Ps cols nhs, ∃ a, σ (.n q'.1) = ptrAt a ∧ ∀ o < q'.2, R (a + o) := by
    intro σ j hj v9 v8 p4 p5 q' hq'
    simp only [lr2Ps, List.mem_cons, List.not_mem_nil, or_false] at hq'
    rcases hq' with rfl | rfl | rfl | rfl
    · exact ⟨irow, p4, hR.2.1⟩
    · exact ⟨ihs, p5, hR.2.2.1⟩
    · refine ⟨ip + resBatch * b + j, v9, fun o ho => ?_⟩
      rw [Nat.add_assoc, Nat.add_assoc]; exact hR.1 _ (by simp only at ho; omega)
    · refine ⟨ic + 2 * b + 2 * j, v8, fun o ho => ?_⟩
      rw [Nat.add_assoc, Nat.add_assoc]; exact hR.2.2.2 _ (by simp only at ho; omega)
  intro m
  induction m with
  | zero =>
    intro j hj rd t hn hv hbt
    have h := shapeR_loopFlat (fs := fs) (al := al)
      (args := lr2Args j r (ic + 2 * b) (ip + resBatch * b) irow ihs mu) (R := R)
      (Bt := lpB fs name r (j + 1)) hfind (by rw [hbody]; exact hb') hls hok ?_ rd t hn hv hbt
    · have e : fs name + lpB fs name r (j + 1) = lpB fs name r j := by
        simp only [lpB]; rw [show r - j = (r - (j + 1)) + 1 by omega]; ring
      rwa [e] at h
    · intro rd' σ hp hA
      have hp' : ∀ i < 7, σ (.n i) = (lr2Args j r (ic + 2 * b) (ip + resBatch * b) irow ihs mu).getD i 0 :=
        fun i hi => param_of_map (by rw [← hpar]; exact hp) hi
      obtain ⟨v9, v8, p4, p5, -, vg, -⟩ := lr2_vals hp' fun a ha _ => hA a (mem_atomsOf' ha)
      refine ⟨hbase σ j (by omega) v9 v8 p4 p5, fun _ => by simp only [lpB]; rw [show r - (j + 1) = 0 by omega]; ring,
        fun hz => ?_⟩
      exact absurd (by rw [vg, show j + 1 = r by omega]; exact CharTwo.add_self_eq_zero _) hz
  | succ m IH =>
    intro j hj rd t hn hv hbt
    have h := shapeR_loopFlat (fs := fs) (al := al)
      (args := lr2Args j r (ic + 2 * b) (ip + resBatch * b) irow ihs mu) (R := R)
      (Bt := lpB fs name r (j + 1)) hfind (by rw [hbody]; exact hb') hls hok ?_ rd t hn hv hbt
    · have e : fs name + lpB fs name r (j + 1) = lpB fs name r j := by
        simp only [lpB]; rw [show r - j = (r - (j + 1)) + 1 by omega]; ring
      rwa [e] at h
    · intro rd' σ hp hA
      have hp' : ∀ i < 7, σ (.n i) = (lr2Args j r (ic + 2 * b) (ip + resBatch * b) irow ihs mu).getD i 0 :=
        fun i hi => param_of_map (by rw [← hpar]; exact hp) hi
      obtain ⟨v9, v8, p4, p5, -, vg, vt⟩ := lr2_vals hp' fun a ha _ => hA a (mem_atomsOf' ha)
      refine ⟨hbase σ j (by omega) v9 v8 p4 p5, fun hz => absurd hz ?_, fun _ t' hn' hv' hb'' => ?_⟩
      · rw [vg]; exact (gen_add_ne' (by omega) (by omega)).not.mpr (by omega)
      · rw [vt] at hv'
        exact IH (j + 1) (by omega) rd' t' hn' hv' hb''

end
end LeanVM.Guest.B1.VsC
