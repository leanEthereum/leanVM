/-
  LeanVM.Guest.B1.Da.VerifyAt

  `da_verify` placed by the bump allocator, loading from a region (`RelAtIn`): its seven
  `HeapBuf`s after its frame, its counters' run in its frame, its callees after its `HeapBuf`s.
-/

module

public import LeanVM.Guest.B1.Da.Complete
public import LeanVM.Guest.B1.Da.SetupIn

/-!
# `da_verify`, placed

At `fp`, `da_verify` allocates `prefix_digests` (`128N` words), `prefix_bases` (`r`), `hashes`
(`258`), the row sums' chains (`129r`), `rowbase` (`r`), `coltree` (`512`) and `rowtree` (`4N`)
from `fp + fs "da_verify"`, and takes its counter words' run in its frame. Its callees follow:
`da_row_shape`, `__loop88`, `__loop89`, the column loops (whose columns `dvPtrs` places), `__loop92`,
the column tree, `__loop93`, `__loop94` and the row tree. `dvPtrs` is `DaPtrs` at those positions;
on a memory holding the honest words there, `da_verify` holds placed, loading only
`g_squares[lp]` outside its own data.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Main (RelAtInW relAtInW_of_walk KidsFromInW)

@[expose] public section

/-! ## The placement -/

/-- `da_verify`'s `HeapBuf` sizes. -/
def dvSizes (r N : ℕ) : List ℕ := [128 * N, r, 258, 129 * r, r, 512, 4 * N]

/-- The words of `da_verify`'s callees, in call order. -/
def dvKids (fs : String → ℕ) (r N lp : ℕ) : List ℕ :=
  [fs "da_row_shape", (r - 0) * fs "__loop88" + fs "__loop88", (r - 0) * fs "__loop89" + fs "__loop89",
   clTot fs true r N lp 0, clTot fs false r N lp 64, (r - 0) * fs "__loop92" + fs "__loop92", dlTot fs 7,
   (r - 0) * fs "__loop93" + fs "__loop93",
   if N - r = 0 then fs "__loop94" else (N - r - 0) * fs "__loop94" + fs "__loop94", dlTot fs lp]

/-- The position of `da_verify`'s callees. -/
def dvK0 (fs : String → ℕ) (fp r N : ℕ) : ℕ := fp + fs "da_verify" + (dvSizes r N).sum

/-- The positions of the column loops. -/
def dvPos90 (fs : String → ℕ) (fp r N : ℕ) : ℕ :=
  dvK0 fs fp r N + fs "da_row_shape" + ((r - 0) * fs "__loop88" + fs "__loop88") +
    ((r - 0) * fs "__loop89" + fs "__loop89")
def dvPos91 (fs : String → ℕ) (fp r N lp : ℕ) : ℕ := dvPos90 fs fp r N + clTot fs true r N lp 0

/-- The frame position of column `b`. -/
def dvColPos (fs : String → ℕ) (fp r N lp b : ℕ) : ℕ :=
  colPos fs (decide (b < 64)) r N lp (if b < 64 then dvPos90 fs fp r N else dvPos91 fs fp r N lp) b

/-- **`da_verify`'s pointers at `fp`**, as the bump allocator and the certificate place them. -/
def dvPtrs (fs : String → ℕ) (cert : String → V → ℕ) (r : ℕ) (fp : ℕ) : DaPtrs :=
  let N := LeanDa.nPad r
  let lp := LeanDa.logPad r
  let b0 := fp + fs "da_verify"
  { pd := gen ^ b0, pb := gen ^ (b0 + 128 * N), hs := gen ^ (b0 + 128 * N + r),
    acc := gen ^ (b0 + 128 * N + r + 258), rb := gen ^ (b0 + 128 * N + r + 258 + 129 * r),
    ct := gen ^ (b0 + 128 * N + r + 258 + 129 * r + r),
    rt := gen ^ (b0 + 128 * N + r + 258 + 129 * r + r + 512),
    ctr := gen ^ (fp + cert "da_verify" (.n 20)),
    node := fun b => gen ^ (dvColPos fs fp r N lp b + fs (colName (decide (b < 64)))),
    lv := fun b => gen ^ (dvColPos fs fp r N lp b + fs (colName (decide (b < 64))) + 4 * N +
      fs "da_vector_dispatch" + cert (vxName (decide (b = 127))) (.n 4)) }

/-- The words of `da_verify`. -/
def dvTot (fs : String → ℕ) (r : ℕ) : ℕ :=
  fs "da_verify" + (dvSizes r (LeanDa.nPad r)).sum +
    ((dvKids fs r (LeanDa.nPad r) (LeanDa.logPad r)).foldr (· + ·) 0)

/-! ## The path -/

def dvPre : List Stmt := dvA ++ dvK.map .atom ++ dvB.take 36
def dvPost : List Stmt := (dvB.drop 37).dropLast

theorem dvB_split : dvB = dvB.take 36 ++ .dispatch (.n 2) dlNames [.n 429] [.n 436, .n 437] ::
    (dvPost ++ [.ret [.n 443, .n 444, .n 445, .n 446]]) := rfl

theorem dvBody_split : dvBody = dvPre ++ .dispatch (.n 2) dlNames [.n 429] [.n 436, .n 437] ::
    (dvPost ++ [.ret [.n 443, .n 444, .n 445, .n 446]]) := by
  rw [dvBody, dvPre, List.append_assoc, List.append_assoc, List.append_assoc]
  congr 2

theorem dvPre_straight : dvPre.all Main.Stmt.straight = true := by decide +kernel
theorem dvPost_straight : dvPost.all Main.Stmt.straight = true := by decide +kernel

theorem sqIter_gen (e : ℕ) : ∀ k, sqIter (gen ^ e) k = gen ^ (2 ^ k * e)
  | 0 => by simp [sqIter]
  | k + 1 => by rw [sqIter, sqIter_gen e k, ← pow_add]; congr 1; ring

/-! ## The pure callees -/

theorem pure_one {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hb : Stmt.pureList [f] fn.body = true) : coreProgram.PureIn [f] := by
  intro g hg fn' hf'
  rw [List.mem_singleton] at hg
  subst hg
  rw [hf, Option.some.injEq] at hf'
  subst hf'
  exact hb

theorem drs_pure : coreProgram.PureIn ["da_row_shape"] := pure_one find_da_row_shape (by decide +kernel)
theorem l88_pure : coreProgram.PureIn ["__loop88"] := pure_one find_l88 (by decide +kernel)
theorem l89_pure : coreProgram.PureIn ["__loop89"] := pure_one find_l89 (by decide +kernel)
theorem l92_pure : coreProgram.PureIn ["__loop92"] := pure_one find_l92 (by decide +kernel)
theorem l93_pure : coreProgram.PureIn ["__loop93"] := pure_one find_l93 (by decide +kernel)
theorem l94_pure : coreProgram.PureIn ["__loop94"] := pure_one find_l94 (by decide +kernel)

/-! ## The placed relation -/

/-- **`da_verify` at `fp`**: a witness opening `(root, vd)`, on a memory holding the honest words at
`dvPtrs` and the squares table at `gsq`, holds placed by a tree of `dvTot` words loading only
`g_squares[logPad r]` outside its own data, at a word of `R`. -/
theorem dv_relAtIn (fs : String → ℕ) (cert : String → V → ℕ) {rd : Reader} (hl : Low16 rd) {gsq : E}
    (hT : SquaresAt rd gsq) {root vd : Digest} {w : Da.Witness} (hw : w.Opens root vd) {R : ℕ → Prop}
    (hR : ∃ i, (gsq * gen ^ LeanDa.logPad w.rows.length).limb 0 * gpow 0 = gpow i ∧ R i) (fp : ℕ)
    (hP : DaMem rd (dvPtrs fs cert w.rows.length fp) w) :
    RelAtInW fs cert wId rd R (fun _ => False) fp (dvTot fs w.rows.length) "da_verify" [gsq]
      [(digestScalars root).1, (digestScalars root).2, (digestScalars vd).1, (digestScalars vd).2]
      fun θ => dvTot θ w.rows.length := by
  obtain ⟨hcol, hr1, hr2, h88, hiv0, hiv1, hkc, hctr, h89, h92, hlv7, h93, h94, hlvr, hfin, hv0, hv1⟩ :=
    daMem_parts hw _ hP
  set r := w.rows.length with hr
  set N := LeanDa.nPad r with hNd
  set lp := LeanDa.logPad r with hlpd
  have hr33 : r < 2 ^ 33 := by unfold LeanDa.maxRows at hr2; omega
  have hN := nPad_le hr2
  have hlp : lp ≤ 10 := logPad_le hr2
  have hrN : r ≤ N := ((logPad_iff (lp := lp) hr1).mp rfl).1
  have hNp : N = 2 ^ lp := rfl
  have hvl := hw.2.2.2.2.1
  set P := dvPtrs fs cert r fp with hPd
  -- the columns
  have hcolM : ∀ b < 128, Meaning_da_verify_column (decide (b < 64)) rd
      [gen ^ b, gen ^ r, gen ^ N, gen ^ (N - r), gen ^ lp, P.pb, P.ct, P.rb, P.hs, P.ctr] [] := fun b hb => by
    obtain ⟨hcm, hch⟩ := hcol b hb
    have hwl : (daWs w b).length = 256 := length_chunk (n := 128) hvl hb
    exact colMeaning_of_mem hb hr1 hr33 (by omega) (by omega) hwl (by simp) hcm hch (isInK_gen_pow _)
  have hholds := dv_holds hl hT hr1 hr2 h88 hiv0 hiv1 hkc hctr h89 hcolM h92 hlv7 h93 h94 hlvr hfin hv0 hv1
  set σ : Val := fun v => dvVals (gsq) (gen ^ r) (gen ^ lp) (gen ^ N) (gen ^ (N - r)) P.pd P.pb P.hs P.ctr
    P.acc P.rb P.ct P.rt (digestScalars (colRootOf r (daSym w))).1 (digestScalars (colRootOf r (daSym w))).2
    (digestScalars (rowRootOf r (daSym w))).1 (digestScalars (rowRootOf r (daSym w))).2 (digestScalars root).1
    (digestScalars root).2 (digestScalars vd).1 (digestScalars vd).2 v.idx with hσ
  have hx : σ (.n 2) = ofK (gpow lp) := by rw [← gen_pow_eq_ofK]; rfl
  have hw' := walk_dispatch σ dvPre dvPost dvPre_straight dvPost_straight (.n 2) dlNames [.n 429]
    [.n 436, .n 437] [.n 443, .n 444, .n 445, .n 446] (i := lp) (by simp [dlNames]; omega) (by simp [dlNames]) hx
  rw [← dvBody_split] at hw'
  set es := dvPre.flatMap (Main.slEvs σ) ++
    .call dlNames[lp]! [.n 429] [.n 436, .n 437] :: dvPost.flatMap (Main.slEvs σ) with hes
  have hev := holds_of_holdsList find_dv hholds hw'
  obtain ⟨hpd, hpa, hpad, hpc⟩ := Main.straight_parts σ _ dvPre_straight
  obtain ⟨hqd, hqa, hqad, hqc⟩ := Main.straight_parts σ _ dvPost_straight
  have hpaS : dvPre.filterMap Main.Stmt.allocSz = [(.n 12, .inr (.n 11)), (.n 13, .inr (.n 1)), (.n 17, .inl 258),
      (.n 414, .inr (.n 413)), (.n 415, .inr (.n 1)), (.n 419, .inl 512), (.n 429, .inr (.n 428))] := by
    decide +kernel
  have hqaS : dvPost.filterMap Main.Stmt.allocSz = [] := by decide +kernel
  have hlg : ∀ {e : ℕ}, e < 2 ^ 64 - 1 → logG (gen ^ e) = e := fun he => logG_gen_pow he
  have h11 : σ (.n 11) = gen ^ (128 * N) := by
    show sqIter (gen ^ N) 7 = _; rw [sqIter_gen, show 2 ^ 7 * N = 128 * N by norm_num]
  have h413 : σ (.n 413) = gen ^ (129 * r) := by
    show sqIter (gen ^ r) 7 * gen ^ r = _
    rw [sqIter_gen, ← pow_add, show 2 ^ 7 * r + r = 129 * r by norm_num; ring]
  have h428 : σ (.n 428) = gen ^ (4 * N) := by
    show gen ^ N * gen ^ N * (gen ^ N * gen ^ N) = _; ring
  have hal : allocs σ es = dvSizes r N := by
    rw [hes, allocs_append, show allocs σ (.call dlNames[lp]! [.n 429] [.n 436, .n 437] ::
      dvPost.flatMap (Main.slEvs σ)) = allocs σ (dvPost.flatMap (Main.slEvs σ)) from rfl, hpa, hqa, hpaS, hqaS]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, Sum.elim_inl, id, h11, h413, h428, List.append_nil]
    rw [show σ (.n 1) = gen ^ r from rfl, hlg (show r < 2 ^ 64 - 1 by omega),
      hlg (show 128 * N < 2 ^ 64 - 1 by omega), hlg (show 129 * r < 2 ^ 64 - 1 by omega),
      hlg (show 4 * N < 2 ^ 64 - 1 by omega)]
    rfl
  -- the data
  set b0 := fp + fs "da_verify" with hb0
  have hzip : (dvSizes r N).zip (bases b0 (dvSizes r N)) = [(128 * N, b0), (r, b0 + 128 * N),
      (258, b0 + 128 * N + r), (129 * r, b0 + 128 * N + r + 258), (r, b0 + 128 * N + r + 258 + 129 * r),
      (512, b0 + 128 * N + r + 258 + 129 * r + r), (4 * N, b0 + 128 * N + r + 258 + 129 * r + r + 512)] := rfl
  have hruns : runs es = [(.n 20, 385)] := by
    rw [hes, runs_append, show runs (.call dlNames[lp]! [.n 429] [.n 436, .n 437] ::
      dvPost.flatMap (Main.slEvs σ)) = runs (dvPost.flatMap (Main.slEvs σ)) from rfl,
      runs_straight σ _ dvPre_straight, runs_straight σ _ dvPost_straight,
      show dvPre.filterMap stmtRun? = [(.n 20, 385)] by decide +kernel,
      show dvPost.filterMap stmtRun? = [] by decide +kernel]
    rfl
  have hO : ∀ {k i : ℕ}, ∀ q ∈ (dvSizes r N).zip (bases b0 (dvSizes r N)), q.2 + k = i → k < q.1 →
      ownData cert fp b0 "da_verify" (dvSizes r N) es i := fun q hq h1 h2 => Or.inl ⟨q, hq, by omega, by omega⟩
  have hC : ∀ {i : ℕ}, fp + cert "da_verify" (.n 20) ≤ i → i < fp + cert "da_verify" (.n 20) + 385 →
      ownData cert fp b0 "da_verify" (dvSizes r N) es i := fun h1 h2 =>
    Or.inr ⟨(.n 20, 385), by rw [hruns]; exact List.Mem.head _, h1, h2⟩
  -- the frames
  have hpcS : dvPre.filterMap Main.Stmt.callS = [(none, "da_row_shape", [.n 1, .n 2, .n 0], [.n 3, .n 4]),
      (some (.n 15), "__loop88", [.n 16, .n 1, .n 13, .n 12], []),
      (some (.n 417), "__loop89", [.n 418, .n 1, .n 414, .n 415], []),
      (none, "__loop90", [.n 420, .n 1, .n 3, .n 4, .n 2, .n 13, .n 419, .n 415, .n 17, .n 405], []),
      (none, "__loop91", [.n 421, .n 1, .n 3, .n 4, .n 2, .n 13, .n 419, .n 415, .n 17, .n 405], []),
      (some (.n 423), "__loop92", [.n 424, .n 1, .n 415], []),
      (none, "da_levels__L128_L7", [.n 419], [.n 425, .n 426]),
      (some (.n 431), "__loop93", [.n 432, .n 1, .n 13, .n 429], []),
      (some (.n 434), "__loop94", [.n 435, .n 4, .n 429, .n 1], [])] := by decide +kernel
  have hk1 : decide (1 + gen ^ r ≠ (0 : E)) = true :=
    decide_eq_true (one_add_ne_zero.mpr fun he => by have := (gen_pow_eq_one_iff (by omega)).mp he; omega)
  have hgapd : decide (1 + gen ^ (N - r) ≠ (0 : E)) = decide (N - r ≠ 0) := by
    refine decide_eq_decide.mpr ⟨fun h he => h (by rw [he, pow_zero]; exact e_add_eq_zero_iff.mpr rfl),
      fun h he => h ((gen_pow_eq_one_iff (show N - r < 2 ^ 64 - 1 by omega)).mp (e_add_eq_zero_iff.mp he).symm)⟩
  have hcalls : calls es = [⟨"da_row_shape", [.n 1, .n 2, .n 0], [.n 3, .n 4], true⟩,
      ⟨"__loop88", [.n 16, .n 1, .n 13, .n 12], [], true⟩,
      ⟨"__loop89", [.n 418, .n 1, .n 414, .n 415], [], true⟩,
      ⟨"__loop90", [.n 420, .n 1, .n 3, .n 4, .n 2, .n 13, .n 419, .n 415, .n 17, .n 405], [], true⟩,
      ⟨"__loop91", [.n 421, .n 1, .n 3, .n 4, .n 2, .n 13, .n 419, .n 415, .n 17, .n 405], [], true⟩,
      ⟨"__loop92", [.n 424, .n 1, .n 415], [], true⟩,
      ⟨"da_levels__L128_L7", [.n 419], [.n 425, .n 426], true⟩,
      ⟨"__loop93", [.n 432, .n 1, .n 13, .n 429], [], true⟩,
      ⟨"__loop94", [.n 435, .n 4, .n 429, .n 1], [], decide (N - r ≠ 0)⟩,
      ⟨dlNames[lp]!, [.n 429], [.n 436, .n 437], true⟩] := by
    rw [hes, calls_append, show calls (.call dlNames[lp]! [.n 429] [.n 436, .n 437] ::
      dvPost.flatMap (Main.slEvs σ)) = ⟨dlNames[lp]!, [.n 429], [.n 436, .n 437], true⟩ ::
        calls (dvPost.flatMap (Main.slEvs σ)) from rfl, hpc, hqc, hpcS,
      show dvPost.filterMap Main.Stmt.callS = [] by decide +kernel]
    simp only [List.map_cons, List.map_nil, Main.mkCall, List.cons_append, List.nil_append]
    rw [show σ (.n 15) = 1 + gen ^ r from rfl, show σ (.n 417) = 1 + gen ^ r from rfl,
      show σ (.n 423) = 1 + gen ^ r from rfl, show σ (.n 431) = 1 + gen ^ r from rfl,
      show σ (.n 434) = 1 + gen ^ (N - r) from rfl, hk1, hgapd]
  -- the pointers' exponents
  set Dx := b0
  set Px := b0 + 128 * N
  set Hx := Px + r
  set Ax := Hx + 258
  set Bx := Ax + 129 * r
  set Tx := Bx + r
  set Wx := Tx + 512
  set Cx := fp + cert "da_verify" (.n 20)
  have hmemZ : ∀ {q : ℕ × ℕ}, q ∈ [(128 * N, Dx), (r, Px), (258, Hx), (129 * r, Ax), (r, Bx), (512, Tx),
      (4 * N, Wx)] → q ∈ (dvSizes r N).zip (bases b0 (dvSizes r N)) := fun h => by rw [hzip]; exact h
  have oD : ∀ {k : ℕ}, k < 128 * N → ownData cert fp b0 "da_verify" (dvSizes r N) es (Dx + k) :=
    fun hk => hO (128 * N, Dx) (hmemZ (by simp)) rfl hk
  have oP : ∀ {k : ℕ}, k < r → ownData cert fp b0 "da_verify" (dvSizes r N) es (Px + k) :=
    fun hk => hO (r, Px) (hmemZ (by simp)) rfl hk
  have oH : ∀ {k : ℕ}, k < 258 → ownData cert fp b0 "da_verify" (dvSizes r N) es (Hx + k) :=
    fun hk => hO (258, Hx) (hmemZ (by simp)) rfl hk
  have oA : ∀ {k : ℕ}, k < 129 * r → ownData cert fp b0 "da_verify" (dvSizes r N) es (Ax + k) :=
    fun hk => hO (129 * r, Ax) (hmemZ (by simp)) rfl hk
  have oB : ∀ {k : ℕ}, k < r → ownData cert fp b0 "da_verify" (dvSizes r N) es (Bx + k) :=
    fun hk => hO (r, Bx) (hmemZ (by simp)) rfl hk
  have oT : ∀ {k : ℕ}, k < 512 → ownData cert fp b0 "da_verify" (dvSizes r N) es (Tx + k) :=
    fun hk => hO (512, Tx) (hmemZ (by simp)) rfl hk
  have oW : ∀ {k : ℕ}, k < 4 * N → ownData cert fp b0 "da_verify" (dvSizes r N) es (Wx + k) :=
    fun hk => hO (4 * N, Wx) (hmemZ (by simp)) rfl hk
  have oC : ∀ {k : ℕ}, k < 385 → ownData cert fp b0 "da_verify" (dvSizes r N) es (Cx + k) :=
    fun hk => hC (by omega) (by omega)
  -- the memory's pointers
  have hrb : ∀ j < r, rd (gpow (Bx + j)) = some (gen ^ (Ax + 129 * j)) := fun j hj => by
    have := load_rd (h89 j hj).1
    rw [show P.rb * gen ^ j = gen ^ (Bx + j) by show gen ^ Bx * gen ^ j = _; rw [← pow_add], addr_gen, Nat.add_zero] at this
    rwa [show P.acc * (gen ^ j) ^ 129 = gen ^ (Ax + 129 * j) by
      show gen ^ Ax * (gen ^ j) ^ 129 = _; rw [← pow_mul, ← pow_add, Nat.mul_comm j]] at this
  have hpb : ∀ j < r, rd (gpow (Px + j)) = some (gen ^ (Dx + 128 * j)) := fun j hj => by
    have := load_rd (h88 j hj)
    rw [show P.pb * gen ^ j = gen ^ (Px + j) by show gen ^ Px * gen ^ j = _; rw [← pow_add], addr_gen, Nat.add_zero] at this
    rwa [show P.pd * (gen ^ j) ^ 128 = gen ^ (Dx + 128 * j) by
      show gen ^ Dx * (gen ^ j) ^ 128 = _; rw [← pow_mul, ← pow_add, Nat.mul_comm j]] at this
  -- the callees
  have hdrs : coreProgram.Rel rd "da_row_shape" [gen ^ r, gen ^ lp, gsq] [gen ^ N, gen ^ (N - r)] :=
    da_row_shape_complete hl hT _ _ _ ⟨_, _, _, _, _, rfl, rfl, r, hr1, hr2, rfl, rfl, rfl, rfl⟩
  have k1 := relAtInW_of_relInTW_pure fs cert drs_pure (List.mem_singleton_self _)
    (drs_relInT fs (R := R) hR hdrs)
  have k2 := relAtInW_of_relInTW_pure fs cert l88_pure (List.mem_singleton_self _)
    (l88_relInT fs (R := R88 r Px) hr33 (fun _ h => h) hr1 ((l88_iff rd _ _ _ 0).mpr (loop_of_all hr1 hr33 h88)))
  have k3 := relAtInW_of_relInTW_pure fs cert l89_pure (List.mem_singleton_self _)
    (l89_relInT fs (R := R89 r Ax Bx) hr33 (fun _ h => h) hr1 ((l89_iff rd _ _ _ 0).mpr (loop_of_all hr1 hr33 h89)))
  have k6 := relAtInW_of_relInTW_pure fs cert l92_pure (List.mem_singleton_self _)
    (l92_relInT fs (R := R92 r Ax Bx) hr33 hrb (fun _ h => h) hr1 ((l92_iff rd _ _ 0).mpr (loop_of_all hr1 hr33 h92)))
  have k7 := relAtInW_of_relInTW_pure fs cert (lv_pure (k := 7) (by norm_num)) (by simp [lvSet])
    (levels_relInT fs (k := 7) (by norm_num) (R := TreeR Tx 7) (fun _ h => h) ((da_levels_iff 7 (by norm_num) _ _).mpr hlv7))
  have k8 := relAtInW_of_relInTW_pure fs cert l93_pure (List.mem_singleton_self _)
    (l93_relInT fs (R := R93 r Px Dx Wx) hr33 hpb (fun _ h => h) hr1 ((l93_iff rd _ _ _ 0).mpr (loop_of_all hr1 hr33 h93)))
  have k10 := relAtInW_of_relInTW_pure fs cert (lv_pure hlp) (by simp [lvSet])
    (levels_relInT fs hlp (R := TreeR Wx lp) (fun _ h => h) ((da_levels_iff lp hlp _ _).mpr hlvr))
  rw [pow_zero] at k2 k3 k6 k8
  rw [← dlNames_getElem! (by omega)] at k10
  -- the column loops
  set Rcol : ℕ → Prop := fun i => R i ∨ ownData cert fp b0 "da_verify" (dvSizes r N) es i with hRcol
  have hRc : ∀ b < 128, ∀ k < 4, Rcol (Cx + 3 * b + k) := fun b hb k hk => Or.inr (by
    rw [show Cx + 3 * b + k = Cx + (3 * b + k) by ring]; exact oC (by omega))
  have hRh : ∀ b < 128, ∀ k < 4, Rcol (Hx + 2 * b + k) := fun b hb k hk => Or.inr (by
    rw [show Hx + 2 * b + k = Hx + (2 * b + k) by ring]; exact oH (by omega))
  have hRt : ∀ b < 128, ∀ k < 2, Rcol (Tx + 2 * b + k) := fun b hb k hk => Or.inr (by
    rw [show Tx + 2 * b + k = Tx + (2 * b + k) by ring]; exact oT (by omega))
  have hRrow : ∀ (store : Bool), ∀ b < clHi store, ∀ j < r, Rcol (Bx + j) ∧ Rcol (Ax + 129 * j + b) ∧
      Rcol (Ax + 129 * j + b + 1) ∧ (store = true → Rcol (Px + j) ∧ Rcol (Dx + 128 * j + 2 * b) ∧
        Rcol (Dx + 128 * j + 2 * b + 1)) := fun store b hb j hj =>
    have hb' : b < 128 := by cases store <;> simp [clHi] at hb <;> omega
    ⟨Or.inr (oB hj), Or.inr (by rw [Nat.add_assoc]; exact oA (by nlinarith)),
      Or.inr (by rw [Nat.add_assoc, Nat.add_assoc]; exact oA (by nlinarith)),
      fun hs => have h64 : b < 64 := by subst hs; simpa [clHi] using hb
        ⟨Or.inr (oP hj), Or.inr (by rw [Nat.add_assoc]; exact oD (by nlinarith)),
        Or.inr (by rw [Nat.add_assoc, Nat.add_assoc]; exact oD (by nlinarith))⟩⟩
  have hmemC : ∀ (store : Bool) (fp0 : ℕ), (∀ b, clLo store ≤ b → b < clHi store →
      (decide (b < 64) = store ∧ (if b < 64 then dvPos90 fs fp r N else dvPos91 fs fp r N lp) = fp0)) →
      ∀ b, clLo store ≤ b → b < clHi store → ColAt fs cert store rd b r N lp Px Tx Bx Hx Cx
        (digestScalars (daS w b)).1 (digestScalars (daS w b)).2 (digestScalars (daS w (b + 1))).1
        (digestScalars (daS w (b + 1))).2 (digestScalars (nodeD (colLeafOf r (daSym w) b) lp 0)).1
        (digestScalars (nodeD (colLeafOf r (daSym w) b) lp 0)).2 (daWs w b) ((List.range 4).map (cvOf b))
        (colPos fs store r N lp fp0 b) := fun store fp0 hst b h1 h2 => by
    have hb : b < 128 := by cases store <;> simp [clHi] at h2 <;> omega
    obtain ⟨e1, e2⟩ := hst b h1 h2
    have := (hcol b hb).1
    simp only [hPd, dvPtrs, dvColPos, e1] at this
    rw [e2] at this
    exact this
  have k4 := colLoop_relAtIn fs cert true (R := Rcol) hr1 hrN hNp hlp (WS := daWs w)
    (CV := fun b => (List.range 4).map (cvOf b)) (fun b => by simp) (fun b hb => (hcol b hb).2) hRc hRh hRt
    (hRrow true) (dvPos90 fs fp r N) rd (hmemC true _ fun b h1 h2 => by
      have : b < 64 := by simpa [clHi] using h2
      exact ⟨decide_eq_true this, ite_pos' this _ _⟩) hrb (fun _ => hpb) 0 (by decide) (by decide)
  have k5 := colLoop_relAtIn fs cert false (R := Rcol) hr1 hrN hNp hlp (WS := daWs w)
    (CV := fun b => (List.range 4).map (cvOf b)) (fun b => by simp) (fun b hb => (hcol b hb).2) hRc hRh hRt
    (hRrow false) (dvPos91 fs fp r N lp) rd (hmemC false _ fun b h1 h2 => by
      have : ¬ b < 64 := by simp [clLo] at h1; omega
      exact ⟨decide_eq_false this, ite_neg' this _ _⟩) hrb (fun h => absurd h (by decide)) 64 (by decide) (by decide)
  rw [show (0 : ℕ) - clLo true = 0 from rfl, Nat.zero_mul, Nat.add_zero, pow_zero] at k4
  rw [show (64 : ℕ) - clLo false = 0 from rfl, Nat.zero_mul, Nat.add_zero] at k5
  have hev' : ∀ e ∈ es, e.Holds rd σ := hev
  have h := relAtInW_of_walk (fs := fs) (cert := cert) (w := wId) (σ := σ) (rd := rd)
    (R := R) (D := fun _ => False) (Dk := fun _ => False) (fp := fp)
    (N := (dvKids fs r N lp).foldr (· + ·) 0)
    (bws := [fun θ => θ "da_row_shape", fun θ => (r - 0) * θ "__loop88" + θ "__loop88",
      fun θ => (r - 0) * θ "__loop89" + θ "__loop89", fun θ => clTot θ true r N lp 0,
      fun θ => clTot θ false r N lp 64, fun θ => (r - 0) * θ "__loop92" + θ "__loop92", fun θ => dlTot θ 7,
      fun θ => (r - 0) * θ "__loop93" + θ "__loop93", fun θ => (N - r - 0) * θ "__loop94" + θ "__loop94",
      fun θ => dlTot θ lp]) find_dv (Or.inl (by decide +kernel)) rfl hw' rfl hev'
    (by
      rw [hal, hes, allocDsts_append, show allocDsts (.call dlNames[lp]! [.n 429] [.n 436, .n 437] ::
        dvPost.flatMap (Main.slEvs σ)) = allocDsts (dvPost.flatMap (Main.slEvs σ)) from rfl, hpd, hqd, hpaS, hqaS]
      simp only [List.map_cons, List.map_nil, List.append_nil, ← gen_pow_eq_ofK]
      rfl)
    (fun q hq => by
      rw [hes, addrs_append, show addrs (.call dlNames[lp]! [.n 429] [.n 436, .n 437] ::
        dvPost.flatMap (Main.slEvs σ)) = addrs (dvPost.flatMap (Main.slEvs σ)) from rfl, hpad, hqad,
        show dvPre.filterMap Main.Stmt.addrS = [(.n 405, .n 20)] by decide +kernel,
        show dvPost.filterMap Main.Stmt.addrS = [] by decide +kernel] at hq
      simp only [List.append_nil, List.mem_singleton] at hq
      subst hq
      rw [← gen_pow_eq_ofK]; rfl)
    ?_ ?_ (fun _ h => h.elim)
  · rw [hal] at h
    refine h.wmono fun θ => ?_
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, dvTot, dvKids, List.foldr, wId,
      Nat.sub_zero, ← hNd, ← hlpd]
    split_ifs with h0
    · rw [h0, Nat.zero_mul, Nat.zero_add]; omega
    · omega
  · rw [hcalls, hal]
    refine ⟨_, _, R, fun _ => False, rfl, fun i hi => Or.inl (Or.inl hi), k1 _, ?_⟩
    refine ⟨_, _, R88 r Px, fun _ => False, rfl, fun i hi => ?_, k2 _, ?_⟩
    · obtain ⟨j, hj, rfl⟩ := hi; exact Or.inl (Or.inr (oP hj))
    refine ⟨_, _, R89 r Ax Bx, fun _ => False, rfl, fun i hi => ?_, k3 _, ?_⟩
    · obtain ⟨j, hj, rfl | rfl⟩ := hi
      · exact Or.inl (Or.inr (oB hj))
      · exact Or.inl (Or.inr (oA (by omega)))
    refine ⟨_, _, Rcol, fun _ => False, rfl, fun i hi => Or.inl hi, k4, ?_⟩
    refine ⟨_, _, Rcol, fun _ => False, rfl, fun i hi => Or.inl hi, k5, ?_⟩
    refine ⟨_, _, R92 r Ax Bx, fun _ => False, rfl, fun i hi => ?_, k6 _, ?_⟩
    · obtain ⟨j, hj, rfl | rfl⟩ := hi
      · exact Or.inl (Or.inr (oB hj))
      · exact Or.inl (Or.inr (by rw [Nat.add_assoc]; exact oA (by omega)))
    refine ⟨_, _, TreeR Tx 7, fun _ => False, rfl, fun i hi => ?_, k7 _, ?_⟩
    · obtain ⟨h1, h2⟩ := hi
      have := oT (k := i - Tx) (by norm_num at h2; omega)
      rw [Nat.add_sub_cancel' h1] at this
      exact Or.inl (Or.inr this)
    refine ⟨_, _, R93 r Px Dx Wx, fun _ => False, rfl, fun i hi => ?_, k8 _, ?_⟩
    · obtain ⟨j, hj, rfl | ⟨h1, h2⟩ | rfl | rfl⟩ := hi
      · exact Or.inl (Or.inr (oP hj))
      · have := oD (k := i - Dx) (by omega)
        rw [Nat.add_sub_cancel' (by omega)] at this
        exact Or.inl (Or.inr this)
      · exact Or.inl (Or.inr (oW (by omega)))
      · exact Or.inl (Or.inr (by rw [Nat.add_assoc]; exact oW (by omega)))
    have hlast : ∀ {Dacc : ℕ → Prop} {b : ℕ}, KidsFromInW fs cert wId rd σ
        (fun i => R i ∨ ownData cert fp b0 "da_verify" (dvSizes r N) es i) Dacc
        [⟨dlNames[lp]!, [.n 429], [.n 436, .n 437], true⟩] [fun θ => dlTot θ lp] b (dlTot fs lp + 0)
        (fun _ => False) :=
      ⟨_, _, TreeR Wx lp, fun _ => False, rfl, fun i hi => ?_, k10 _, rfl, fun i hi => hi.elim⟩
    · by_cases hG : N - r = 0
      · refine ⟨_, _, fun _ => False, fun _ => False, rfl, fun i hi => hi.elim, ?_, ?_⟩
        · simp only [hG, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
        · simp only [hG, ↓reduceIte]
          exact hlast
      · have hGp : 0 < N - r := by omega
        have k9 := relAtInW_of_relInTW_pure fs cert l94_pure (List.mem_singleton_self _)
          (l94_relInT fs (G := N - r) (T := Wx) (r := r) (R := R94 (N - r) Wx r) (by omega) (fun _ h => h) hGp
            ((l94_iff rd _ _ _ 0).mpr (loop_of_all hGp (by omega) h94)))
        rw [pow_zero] at k9
        refine ⟨_, _, R94 (N - r) Wx r, fun _ => False, rfl, fun i hi => ?_, ?_, ?_⟩
        · obtain ⟨d, hd, rfl | rfl⟩ := hi
          · exact Or.inl (Or.inr (oW (by omega)))
          · exact Or.inl (Or.inr (by rw [Nat.add_assoc]; exact oW (by omega)))
        · simp only [ne_eq, hG, not_false_eq_true, decide_true, ↓reduceIte]
          exact k9 _
        · simp only [hG, ↓reduceIte]
          exact hlast
    · obtain ⟨h1, h2⟩ := hi
      have := oW (k := i - Wx) (by rw [← hNp] at h2; omega)
      rw [Nat.add_sub_cancel' h1] at this
      exact Or.inl (Or.inr this)
  · intro A hA
    rw [hes, loadAddrs_append, show loadAddrs σ (.call dlNames[lp]! [.n 429] [.n 436, .n 437] ::
      dvPost.flatMap (Main.slEvs σ)) = loadAddrs σ (dvPost.flatMap (Main.slEvs σ)) from rfl,
      loadAddrs_straight σ _ dvPre_straight, loadAddrs_straight σ _ dvPost_straight,
      show dvPre.filterMap stmtLoad? = [(.n 17, 0), (.n 17, 1)] by decide +kernel,
      show dvPost.filterMap stmtLoad? = [(.n 17, 256), (.n 17, 257)] by decide +kernel] at hA
    have g17 : σ (.n 17) = gen ^ Hx := rfl
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false] at hA
    rw [hal]
    rcases hA with rfl | rfl | rfl | rfl
    · exact ⟨_, by rw [g17, addr_gen], Or.inl (oH (by norm_num))⟩
    · exact ⟨_, by rw [g17, addr_gen], Or.inl (oH (by norm_num))⟩
    · exact ⟨_, by rw [g17, addr_gen], Or.inl (oH (by norm_num))⟩
    · exact ⟨_, by rw [g17, addr_gen], Or.inl (oH (by norm_num))⟩

/-- **The uniform placed form.** -/
theorem dv_relAtIn_uniform (fs : String → ℕ) (cert : String → V → ℕ) {gsq : E} {root vd : Digest}
    {w : Da.Witness} (hw : w.Opens root vd) {R : ℕ → Prop}
    (hR : ∃ i, (gsq * gen ^ LeanDa.logPad w.rows.length).limb 0 * gpow 0 = gpow i ∧ R i) :
    ∀ fp, ∃ n, ∀ rd, (Low16 rd ∧ SquaresAt rd gsq ∧ DaMem rd (dvPtrs fs cert w.rows.length fp) w) →
      RelAtIn coreProgram fs cert rd R (fun _ => False) fp n "da_verify" [gsq]
        [(digestScalars root).1, (digestScalars root).2, (digestScalars vd).1, (digestScalars vd).2] :=
  fun fp => ⟨_, fun _ hm => (dv_relAtIn fs cert hm.1 hm.2.1 hw hR fp hm.2.2).toRelAtIn⟩

end
end LeanVM.Guest.B1.Digest
