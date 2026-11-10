/-
  LeanVM.Guest.B1.Place.OsSqGroup

  A level's query positions placed on f128: the first squeeze's `decode_query_windows`, then the
  squeeze loop, as one group of callees whose window runs depend on where it is placed.
-/

module

public import LeanVM.Guest.B1.Place.SqAt
public import LeanVM.Guest.B1.Place.OsKidsP

/-!
# A level's decoders, placed

A level of `open_stacked` decodes its first squeeze's word by a direct `decode_query_windows`
call, then the other `n - 1` by the squeeze loop entered at `g` (`Whir.osSqueezes`). Placed at
`b`: decoder `0` at `b`, the loop at `b + fs D`, its iteration `t`'s decoder at `sqDecAt`
(`sqDecPos`). The group claims the decoders' `wins` runs (`sqGroupRuns`) and reads the caller's
words `Lk` and the window pointers into those runs (`sqW`: `query_win_ptrs` from the level's
offset, `sqWinPtrs`).

`os_sq_group`: on every memory holding `Lk` with the window table, the capacity chain in the
squeeze run's rows `1 .. n - 1` and the decoded positions, the two calls are placed from any `b`
in `fs D + sqTot` words; `os_sq_groupD`, `os_sq_groupB` the group forms.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier hiding Layout
open LeanVM.Guest.B1.Main (Layout MemL RegionL)
open LeanVM.Guest.B1.Whir

@[expose] public section

/-! ## Pointers -/

theorem ofK_addr_mul_gen_pow (a m : ℕ) :
    ofK (Parameters.addressOfIndex a) * gen ^ m = ofK (Parameters.addressOfIndex (a + m)) := by
  rw [gen_pow_eq_ofK, ← ofK_mul]
  congr 1
  simp only [Parameters.addressOfIndex, pow_add]

theorem ofK_addr_shift (a o j p : ℕ) :
    ofK (Parameters.addressOfIndex a) * gen ^ o * (gen ^ j) ^ p =
      ofK (Parameters.addressOfIndex (a + o + j * p)) := by
  rw [← pow_mul, ofK_addr_mul_gen_pow, ofK_addr_mul_gen_pow]

theorem loadHolds_ofK_iff {rd : Reader} {a k b k' : ℕ} {v : E} (h : a + k = b + k') :
    LoadHolds rd (ofK (Parameters.addressOfIndex a)) k v ↔
      LoadHolds rd (ofK (Parameters.addressOfIndex b)) k' v := by
  unfold LoadHolds
  rw [Main.addr_ofK, Main.addr_ofK, h]
  simp [ofK_isInK]

theorem limb_ofK_addr (a t : ℕ) :
    (ofK (Parameters.addressOfIndex a)).limb 0 * Parameters.addressOfIndex t =
      Parameters.addressOfIndex (a + t) := Main.addr_ofK a t

/-- A run's word, loaded. -/
theorem memL_run_load {rd : Reader} {e : ℕ} {ws : List E} (h : MemL rd [(e, ws)]) {k : ℕ}
    (hk : k < ws.length) : LoadHolds rd (ofK (Parameters.addressOfIndex e)) k ws[k] :=
  h _ (List.mem_singleton_self _) k hk

/-! ## The group's layouts -/

/-- Decoder `s`'s frame, the group at `b`: the first squeeze's at `b`, the loop's iteration
`s - 1`'s after it. -/
def sqDecPos (fs : String → ℕ) (lv : OsLv) (L : String) (n b s : ℕ) : ℕ :=
  if s = 0 then b else sqDecAt fs lv L (n - 1) (b + fs (sqDecName lv)) (s - 1)

/-- The positions a squeeze decodes. -/
abbrev sqPer (lv : OsLv) : ℕ := 128 / lv.depth

/-- The group's claimed runs: each decoder's `wins` run, decoder `s` decoding `w s`. -/
def sqGroupRuns (fs : String → ℕ) (cert : String → V → ℕ) (lv : OsLv) (L : String) (n b : ℕ)
    (w : ℕ → E) : Layout :=
  qwRunL cert (sqDecName lv) b lv.depth lv.capDepth (w 0) ++
    sqRuns fs cert lv L (n - 1) (b + fs (sqDecName lv)) (fun t ↦ w (1 + t)) 0

/-- The window pointers the group at `b` stores, position `k` of squeeze `k / per`. -/
def sqWinPtrs (fs : String → ℕ) (cert : String → V → ℕ) (lv : OsLv) (L : String) (n b : ℕ) :
    List E :=
  (List.range (n * sqPer lv)).map fun k ↦
    qwPtrAt cert (sqDecName lv) (sqDecPos fs lv L n b (k / sqPer lv)) lv.depth lv.capDepth
      (k % sqPer lv)

/-- The level's slice of `query_win_ptrs` (at `g^eq`), the group at `b`. -/
def sqW (fs : String → ℕ) (cert : String → V → ℕ) (lv : OsLv) (L : String) (n eq b : ℕ) :
    Layout :=
  [(eq + lv.posOff, sqWinPtrs fs cert lv L n b)]

theorem sqWinPtrs_get {fs : String → ℕ} {cert : String → V → ℕ} {lv : OsLv} {L : String}
    {n b j i : ℕ} (hj : j < n) (hi : i < sqPer lv) :
    ∃ h : j * sqPer lv + i < (sqWinPtrs fs cert lv L n b).length,
      (sqWinPtrs fs cert lv L n b)[j * sqPer lv + i] =
        qwPtrAt cert (sqDecName lv) (sqDecPos fs lv L n b j) lv.depth lv.capDepth i := by
  have hp : 0 < sqPer lv := by omega
  have hlt : j * sqPer lv + i < n * sqPer lv := by
    have : (j + 1) * sqPer lv ≤ n * sqPer lv := Nat.mul_le_mul_right _ hj
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  refine ⟨by simpa [sqWinPtrs] using hlt, ?_⟩
  simp only [sqWinPtrs, List.getElem_map, List.getElem_range]
  rw [show (j * sqPer lv + i) / sqPer lv = j by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hi, Nat.zero_add],
    show (j * sqPer lv + i) % sqPer lv = i by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]]

/-- The window pointers' load, the group at `b`. -/
theorem sqW_load {fs : String → ℕ} {cert : String → V → ℕ} {lv : OsLv} {L : String}
    {n eq b : ℕ} {rd : Reader} (h : MemL rd (sqW fs cert lv L n eq b)) {j i : ℕ} (hj : j < n)
    (hi : i < sqPer lv) :
    LoadHolds rd (ofK (Parameters.addressOfIndex eq) * gen ^ lv.posOff * (gen ^ j) ^ sqPer lv) i
      (qwPtrAt cert (sqDecName lv) (sqDecPos fs lv L n b j) lv.depth lv.capDepth i) := by
  obtain ⟨hk, he⟩ := sqWinPtrs_get (fs := fs) (cert := cert) (L := L) (b := b) hj hi
  have := memL_run_load h hk
  rw [he] at this
  rw [ofK_addr_shift]
  exact (loadHolds_ofK_iff (by ring)).mp this

theorem sqW_region {fs : String → ℕ} {cert : String → V → ℕ} {lv : OsLv} {L : String}
    {n eq b j i : ℕ} (hj : j < n) (hi : i < sqPer lv) :
    RegionL (sqW fs cert lv L n eq b) (eq + lv.posOff + j * sqPer lv + i) := by
  obtain ⟨hk, -⟩ := sqWinPtrs_get (fs := fs) (cert := cert) (L := L) (b := b) hj hi
  exact ⟨_, List.mem_singleton_self _, by omega, by simp only; omega⟩

/-! ## The group, placed -/

/-- **The loop of a level's decoders, placed at `fp`**: entered when `2 ≤ n`, skipped (its frame)
when `n = 1`. -/
theorem os_sq_loop (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) {lv : OsLv} {L : String}
    {fn : Fn} (hfind : coreProgram.find? L = some fn) (hp : fn.params = osParams 6)
    (hb : fn.body = sqLoopBody lv L) (hlp : coreProgram.loop L = true) (hit : SqIterC lv)
    (hdec : QwDecodeAtD fs cert κ lv.depth lv.capDepth (sqDecName lv))
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n < ordG) {w : ℕ → E} {cap : ℕ → List E}
    (hcl : ∀ j, (cap j).length = 5) (hcw : ∀ j, 1 ≤ j → (⟨cap j, []⟩ : Fs).squeeze.1 = w j)
    {sqz qpos qbp tabs : E} {Lin : Layout} (fp : ℕ)
    (hmem : ∀ rd, LowDef κ rd → MemL rd Lin → ∀ j, 1 ≤ j → j < n →
      (∀ i < 5, LoadHolds rd (sqz * (gen ^ j) ^ 5) i ((cap j).getD i 0)) ∧
        ∀ i < 5, LoadHolds rd (sqz * (gen ^ j) ^ 5) (5 + i)
          (((⟨cap j, []⟩ : Fs).squeeze.2.cap).getD i 0))
    (hdmem : ∀ rd, LowDef κ rd → MemL rd Lin → WinTabs rd tabs ∧ ∀ t < n - 1, ∀ i < sqPer lv,
      LoadHolds rd (qpos * gen ^ lv.posOff * (gen ^ (1 + t)) ^ sqPer lv) i
          (eOfNat (qwPosOf lv.depth (w (1 + t)) i)) ∧
        LoadHolds rd (qbp * gen ^ lv.posOff * (gen ^ (1 + t)) ^ sqPer lv) i
          (qwPtrAt cert (sqDecName lv) (sqDecAt fs lv L (n - 1) fp t) lv.depth lv.capDepth i))
    (hrow : ∀ j, 1 ≤ j → j < n → ∀ t < 10, ∃ i,
      (sqz * (gen ^ j) ^ 5).limb 0 * Parameters.addressOfIndex t =
        Parameters.addressOfIndex i ∧ RegionL Lin i)
    (hreg : ∀ t < n - 1, QwRegs lv.depth [w (1 + t),
        qpos * gen ^ lv.posOff * (gen ^ (1 + t)) ^ sqPer lv,
        qbp * gen ^ lv.posOff * (gen ^ (1 + t)) ^ sqPer lv, tabs] (RegionL Lin))
    (σ : Val) (c2 : Call) (h2f : c2.f = L) (h2t : c2.taken = decide (gen + gen ^ n ≠ 0))
    (h2a : c2.args.map σ = [gen, gen ^ n, sqz, qpos, qbp, tabs]) (h2r : c2.rets = []) :
    ∃ L1 : Layout,
      Within (sqRuns fs cert lv L (n - 1) fp (fun t ↦ w (1 + t)) 0 ++ L1) fp
        (sqTot fs lv L (n - 1) 0) ∧
      DisjL (sqRuns fs cert lv L (n - 1) fp (fun t ↦ w (1 + t)) 0 ++ L1) ∧
      ∀ rd, LowDef κ rd →
        MemL rd (sqRuns fs cert lv L (n - 1) fp (fun t ↦ w (1 + t)) 0 ++ L1 ++ Lin) →
        if c2.taken then RelAtIn coreProgram fs cert rd (RegionL Lin)
          (RegionL (sqRuns fs cert lv L (n - 1) fp (fun t ↦ w (1 + t)) 0)) fp
          (sqTot fs lv L (n - 1) 0) c2.f (c2.args.map σ) (c2.rets.map σ)
        else sqTot fs lv L (n - 1) 0 = fs c2.f := by
  have hw : (fun t ↦ (⟨cap (1 + t), []⟩ : Fs).squeeze.1) = fun t ↦ w (1 + t) :=
    funext fun t ↦ hcw (1 + t) (by omega)
  by_cases h2 : 2 ≤ n
  · have hne : gen + gen ^ n ≠ 0 := by
      intro he
      have h0 := (gen_pow_add_eq_zero_iff 0).mp (by rw [pow_zero, one_mul]; exact he)
      have := gen_pow_inj (by have := hn; unfold ordG at this; omega) (by omega) h0
      omega
    obtain ⟨L1, hW1, hD1, hrel1⟩ := sqLoop_relAtIn fs cert κ hfind hp hb hlp hit hdec
      (e := 1) (n := n) (by omega) hn (sqz := sqz) (qpos := qpos) (qbp := qbp) (tabs := tabs)
      (cap := cap) hcl (Lin := Lin) fp
      (fun rd hl hm j hj1 hj ↦ hmem rd hl hm j hj1 hj)
      (fun rd hl hm ↦ ⟨(hdmem rd hl hm).1, fun t ht i hi ↦ by
        rw [hcw (1 + t) (by omega)]; exact (hdmem rd hl hm).2 t ht i hi⟩)
      hrow (fun t ht ↦ by rw [hcw (1 + t) (by omega)]; exact hreg t ht)
    rw [hw] at hW1 hD1 hrel1
    refine ⟨L1, hW1, hD1, fun rd hl hm ↦ ?_⟩
    rw [h2t, decide_eq_true hne]
    simp only [↓reduceIte, h2f, h2a, h2r, List.map_nil]
    have := hrel1 rd hl hm
    rwa [pow_one] at this
  · obtain rfl : n = 1 := by omega
    have h0 : gen + gen = 0 := by
      have := (gen_pow_add_eq_zero_iff (N := gen ^ 1) 0).mpr rfl
      rwa [pow_zero, one_mul, pow_one] at this
    refine ⟨[], fun q hq ↦ by simp [sqRuns] at hq, by simp [sqRuns, DisjL], fun rd _ _ ↦ ?_⟩
    rw [h2t]
    simp [h0, sqTot, h2f]

/-- **A level's decoders, placed at `b`**, in `fs D + sqTot` words. -/
theorem os_sq_group (fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) {lv : OsLv} {L : String}
    {fn : Fn} (hfind : coreProgram.find? L = some fn) (hp : fn.params = osParams 6)
    (hb : fn.body = sqLoopBody lv L) (hlp : coreProgram.loop L = true) (hit : SqIterC lv)
    (hdec : QwDecodeAtD fs cert κ lv.depth lv.capDepth (sqDecName lv))
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n < ordG) {w : ℕ → E} {cap : ℕ → List E}
    (hcl : ∀ j, (cap j).length = 5) (hcw : ∀ j, 1 ≤ j → (⟨cap j, []⟩ : Fs).squeeze.1 = w j)
    {sqz tabs : E} {eqp eq : ℕ} {Lk : Layout}
    (hmem : ∀ rd, LowDef κ rd → MemL rd Lk → WinTabs rd tabs ∧
      (∀ j, 1 ≤ j → j < n →
        (∀ i < 5, LoadHolds rd (sqz * (gen ^ j) ^ 5) i ((cap j).getD i 0)) ∧
        ∀ i < 5, LoadHolds rd (sqz * (gen ^ j) ^ 5) (5 + i)
          (((⟨cap j, []⟩ : Fs).squeeze.2.cap).getD i 0)) ∧
      ∀ j < n, ∀ i < sqPer lv,
        LoadHolds rd (ofK (Parameters.addressOfIndex eqp) * gen ^ lv.posOff * (gen ^ j) ^ sqPer lv) i
          (eOfNat (qwPosOf lv.depth (w j) i)))
    (hrow : ∀ j, 1 ≤ j → j < n → ∀ t < 10, ∃ i,
      (sqz * (gen ^ j) ^ 5).limb 0 * Parameters.addressOfIndex t =
        Parameters.addressOfIndex i ∧ RegionL Lk i)
    (hrp : ∀ j < n, ∀ t < sqPer lv, RegionL Lk (eqp + lv.posOff + j * sqPer lv + t))
    (hrt : ∀ t < 128, ∃ i, tabs.limb 0 * Parameters.addressOfIndex t =
      Parameters.addressOfIndex i ∧ RegionL Lk i)
    (σ : Val) (c1 c2 : Call) (h1f : c1.f = sqDecName lv) (h1t : c1.taken = true)
    (h1a : c1.args.map σ = [w 0, ofK (Parameters.addressOfIndex eqp) * gen ^ lv.posOff,
      ofK (Parameters.addressOfIndex eq) * gen ^ lv.posOff, tabs]) (h1r : c1.rets = [])
    (h2f : c2.f = L) (h2t : c2.taken = decide (gen + gen ^ n ≠ 0))
    (h2a : c2.args.map σ = [gen, gen ^ n, sqz, ofK (Parameters.addressOfIndex eqp),
      ofK (Parameters.addressOfIndex eq), tabs]) (h2r : c2.rets = []) (b : ℕ) :
    ∃ Lown : Layout,
      Within (sqGroupRuns fs cert lv L n b w ++ Lown) b
        (fs (sqDecName lv) + sqTot fs lv L (n - 1) 0) ∧
      DisjL (sqGroupRuns fs cert lv L n b w ++ Lown) ∧
      ∀ (rd : Reader) (R Dacc : ℕ → Prop), LowDef κ rd →
        MemL rd (sqGroupRuns fs cert lv L n b w ++ Lown) →
        MemL rd (Lk ++ sqW fs cert lv L n eq b) →
        (∀ i, RegionL (Lk ++ sqW fs cert lv L n eq b) i → R i ∨ Dacc i) →
        KidsFromIn coreProgram fs cert rd σ R Dacc [c1, c2] b
          (fs (sqDecName lv) + sqTot fs lv L (n - 1) 0)
          (RegionL (sqGroupRuns fs cert lv L n b w)) := by
  set D := sqDecName lv with hD
  set Lin := Lk ++ sqW fs cert lv L n eq b with hLin
  set qpos := ofK (Parameters.addressOfIndex eqp) with hqpos
  set qbp := ofK (Parameters.addressOfIndex eq) with hqbp
  have hLk : ∀ rd, MemL rd Lin → MemL rd Lk := fun rd h ↦ (Main.memL_append.mp h).1
  have hLW : ∀ rd, MemL rd Lin → MemL rd (sqW fs cert lv L n eq b) := fun rd h ↦
    (Main.memL_append.mp h).2
  have hRk : ∀ i, RegionL Lk i → RegionL Lin i := fun i ⟨q, hq, h1, h2⟩ ↦
    ⟨q, List.mem_append_left _ hq, h1, h2⟩
  have hRw : ∀ i, RegionL (sqW fs cert lv L n eq b) i → RegionL Lin i := fun i ⟨q, hq, h1, h2⟩ ↦
    ⟨q, List.mem_append_right _ hq, h1, h2⟩
  have hreg : ∀ j < n, QwRegs lv.depth [w j, qpos * gen ^ lv.posOff * (gen ^ j) ^ sqPer lv,
      qbp * gen ^ lv.posOff * (gen ^ j) ^ sqPer lv, tabs] (RegionL Lin) := by
    intro j hj p hp t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl
    · refine ⟨eqp + lv.posOff + j * sqPer lv + t, ?_, hRk _ (hrp j hj t ht)⟩
      simp only [List.getD_cons_succ, List.getD_cons_zero, hqpos, ofK_addr_shift, limb_ofK_addr]
    · refine ⟨eq + lv.posOff + j * sqPer lv + t, ?_, hRw _ (sqW_region hj ht)⟩
      simp only [List.getD_cons_succ, List.getD_cons_zero, hqbp, ofK_addr_shift, limb_ofK_addr]
    · obtain ⟨i, hi, hR⟩ := hrt t ht
      exact ⟨i, hi, hRk i hR⟩
  -- decoder `0`
  have hreg0 := hreg 0 hn1
  simp only [pow_zero, one_pow, mul_one] at hreg0
  obtain ⟨L0, hW0, hD0, hrel0⟩ := hdec (w 0) (qpos * gen ^ lv.posOff) (qbp * gen ^ lv.posOff) tabs
    Lin b hreg0 fun rd hl hm ↦ by
      obtain ⟨hT, -, hpos⟩ := hmem rd hl (hLk rd hm)
      refine ⟨hT, fun j hj ↦ ⟨?_, ?_⟩⟩
      · have := hpos 0 hn1 j hj
        simpa using this
      · have := sqW_load (hLW rd hm) (b := b) hn1 hj
        simp only [pow_zero, one_pow, mul_one] at this
        simpa [sqDecPos] using this
  -- the loop
  obtain ⟨L1, hW1, hD1, hrel1⟩ := os_sq_loop fs cert κ hfind hp hb hlp hit hdec hn1 hn hcl hcw
    (sqz := sqz) (qpos := qpos) (qbp := qbp) (tabs := tabs) (Lin := Lin) (b + fs D)
    (fun rd hl hm j hj1 hj ↦ (hmem rd hl (hLk rd hm)).2.1 j hj1 hj)
    (fun rd hl hm ↦ ⟨(hmem rd hl (hLk rd hm)).1, fun t ht i hi ↦
      ⟨(hmem rd hl (hLk rd hm)).2.2 (1 + t) (by omega) i hi, by
        have := sqW_load (hLW rd hm) (b := b) (j := 1 + t) (by omega) hi
        simpa [sqDecPos, show 1 + t ≠ 0 by omega] using this⟩⟩)
    (fun j hj1 hj t ht ↦ by
      obtain ⟨i, hi, hR⟩ := hrow j hj1 hj t ht
      exact ⟨i, hi, hRk i hR⟩)
    (fun t ht ↦ hreg (1 + t) (by omega)) σ c2 h2f h2t h2a h2r
  set runs := sqRuns fs cert lv L (n - 1) (b + fs D) (fun t ↦ w (1 + t)) 0 with hruns
  set run0 := qwRunL cert D b lv.depth lv.capDepth (w 0) with hrun0
  have hruns0 : c2.taken = false → runs = [] := fun ht ↦ by
    rw [h2t] at ht
    have he : gen + gen ^ n = 0 := by simpa using ht
    have h0 := (gen_pow_add_eq_zero_iff 0).mp (by rw [pow_zero, one_mul]; exact he)
    have := gen_pow_inj (by have := hn; unfold ordG at this; omega) (by omega) h0
    rw [hruns, show n - 1 = 0 by omega]
    simp [sqRuns]
  have hS : sqGroupRuns fs cert lv L n b w = run0 ++ runs := rfl
  rw [hS]
  have hmid : (runs ++ (L0 ++ L1)).Perm (L0 ++ (runs ++ L1)) := by
    rw [← List.append_assoc, ← List.append_assoc]
    exact List.perm_append_comm.append_right L1
  have hperm : ((run0 ++ runs) ++ (L0 ++ L1)).Perm ((run0 ++ L0) ++ (runs ++ L1)) := by
    rw [List.append_assoc, List.append_assoc]
    exact hmid.append_left run0
  have hDj : DisjL ((run0 ++ L0) ++ (runs ++ L1)) := disj_append hD0 hD1 hW0 hW1 le_rfl
  refine ⟨L0 ++ L1, fun q hq ↦ ?_, hDj.perm hperm.symm fun h ↦ Or.symm h,
    fun rd R Dacc hl hm hmin hR ↦ ?_⟩
  · rcases List.mem_append.mp ((hperm.mem_iff).mp hq) with hq | hq
    · have := hW0 q hq; omega
    · have := hW1 q hq; omega
  have hm' : MemL rd ((run0 ++ L0) ++ (runs ++ L1)) := fun q hq ↦ hm q ((hperm.mem_iff).mpr hq)
  obtain ⟨hm0, hm1⟩ := Main.memL_append.mp hm'
  refine ⟨fs D, sqTot fs lv L (n - 1) 0, RegionL Lin, RegionL run0, rfl, hR, ?_, ?_⟩
  · rw [h1t]
    simp only [↓reduceIte]
    rw [h1f, h1a, h1r, List.map_nil]
    have := hrel0 rd hl (Main.memL_append.mpr ⟨hm0, hmin⟩)
    exact this
  refine ⟨sqTot fs lv L (n - 1) 0, 0, RegionL Lin, RegionL runs, rfl,
    fun i hi ↦ (hR i hi).imp_right Or.inl, hrel1 rd hl (Main.memL_append.mpr ⟨hm1, hmin⟩), rfl,
    fun i hi ↦ ?_⟩
  rcases os_regionL_append hi with hi | hi
  · exact Or.inl (Or.inr ⟨h1t, hi⟩)
  · cases ht : c2.taken
    · rw [hruns0 ht] at hi
      obtain ⟨q, hq, -⟩ := hi
      simp at hq
    · exact Or.inr ⟨rfl, hi⟩

/-- **A level's decoders as a group** (`OsGroupB`, so `OsGroupD` by `toD`). -/
theorem os_sq_groupB(fs : String → ℕ) (cert : String → V → ℕ) (κ : ℕ) {lv : OsLv} {L : String}
    {fn : Fn} (hfind : coreProgram.find? L = some fn) (hp : fn.params = osParams 6)
    (hb : fn.body = sqLoopBody lv L) (hlp : coreProgram.loop L = true) (hit : SqIterC lv)
    (hdec : QwDecodeAtD fs cert κ lv.depth lv.capDepth (sqDecName lv))
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n < ordG) {w : ℕ → E} {cap : ℕ → List E}
    (hcl : ∀ j, (cap j).length = 5) (hcw : ∀ j, 1 ≤ j → (⟨cap j, []⟩ : Fs).squeeze.1 = w j)
    {sqz tabs : E} {eqp eq : ℕ} {Lk : Layout}
    (hmem : ∀ rd, LowDef κ rd → MemL rd Lk → WinTabs rd tabs ∧
      (∀ j, 1 ≤ j → j < n →
        (∀ i < 5, LoadHolds rd (sqz * (gen ^ j) ^ 5) i ((cap j).getD i 0)) ∧
        ∀ i < 5, LoadHolds rd (sqz * (gen ^ j) ^ 5) (5 + i)
          (((⟨cap j, []⟩ : Fs).squeeze.2.cap).getD i 0)) ∧
      ∀ j < n, ∀ i < sqPer lv,
        LoadHolds rd (ofK (Parameters.addressOfIndex eqp) * gen ^ lv.posOff * (gen ^ j) ^ sqPer lv) i
          (eOfNat (qwPosOf lv.depth (w j) i)))
    (hrow : ∀ j, 1 ≤ j → j < n → ∀ t < 10, ∃ i,
      (sqz * (gen ^ j) ^ 5).limb 0 * Parameters.addressOfIndex t =
        Parameters.addressOfIndex i ∧ RegionL Lk i)
    (hrp : ∀ j < n, ∀ t < sqPer lv, RegionL Lk (eqp + lv.posOff + j * sqPer lv + t))
    (hrt : ∀ t < 128, ∃ i, tabs.limb 0 * Parameters.addressOfIndex t =
      Parameters.addressOfIndex i ∧ RegionL Lk i)
    (σ : Val) (c1 c2 : Call) (h1f : c1.f = sqDecName lv) (h1t : c1.taken = true)
    (h1a : c1.args.map σ = [w 0, ofK (Parameters.addressOfIndex eqp) * gen ^ lv.posOff,
      ofK (Parameters.addressOfIndex eq) * gen ^ lv.posOff, tabs]) (h1r : c1.rets = [])
    (h2f : c2.f = L) (h2t : c2.taken = decide (gen + gen ^ n ≠ 0))
    (h2a : c2.args.map σ = [gen, gen ^ n, sqz, ofK (Parameters.addressOfIndex eqp),
      ofK (Parameters.addressOfIndex eq), tabs]) (h2r : c2.rets = []) {B : ℕ}
    (hB : fs (sqDecName lv) + sqTot fs lv L (n - 1) 0 ≤ B) :
    OsGroupB fs cert κ σ [c1, c2] (fun b ↦ Lk ++ sqW fs cert lv L n eq b)
      (fun b ↦ sqGroupRuns fs cert lv L n b w) B := fun b ↦ by
  obtain ⟨Lown, hW, hD, hK⟩ := os_sq_group fs cert κ hfind hp hb hlp hit hdec hn1 hn hcl hcw hmem
    hrow hrp hrt σ c1 c2 h1f h1t h1a h1r h2f h2t h2a h2r b
  exact ⟨_, Lown, hW, hD, hB, hK⟩

end
end LeanVM.Guest.B1
