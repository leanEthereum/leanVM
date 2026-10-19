/-
  LeanVM.Guest.B1.Tables.FlockAt

  `verify_flock` complete in the uniform placed form (`CompleteFlockAt`).
-/

module

public import LeanVM.Guest.B1.Tables.FlockCAll
public import LeanVM.Guest.B1.Tables.StraightAt

/-!
# `verify_flock`, placed

The four `HeapBuf`s at the allocator's bases (`flSizes`), holding the run's words (`flOwn`):
`zerocheck_r`, `flock_pts`, `flock_pts_r1`, `flock_rounds`. `flMem_of`: a memory holding them
and the caller's words, and any memory agreeing with it there, is `FlMem`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.Guest.B1.Sig
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-- The sizes of `verify_flock`'s `HeapBuf`s. -/
def flSizes (τ : ℕ) : List ℕ := [τ + 14, 2 * τ + 32, 64, 4 * τ + 40]

/-- `zerocheck_r`: the coordinates from offset 6. -/
def flW11 (τ : ℕ) (cv : Digest) : List E :=
  (List.range (τ + 14)).map fun j => if j < 6 then 0 else flE τ cv (j - 6)

/-- `flock_pts`: the squeezes' states from row 13. -/
def flW24 (τ : ℕ) (cv : Digest) : List E :=
  (List.range (2 * τ + 32)).map fun i => if 26 ≤ i ∧ i < 2 * τ + 30 then
    (if i % 2 = 0 then (digestScalars (sqCv^[(i - 26) / 2] cv)).1
      else (digestScalars (sqCv^[(i - 26) / 2] cv)).2) else 0

/-- `flock_pts_r1`: round 1's words. -/
def flW40 (xs : List E) : List E := (List.range 64).map fun i => xs.getD i 0

/-- A word of `flock_rounds`' row `i / 4`. -/
def flRow (τ : ℕ) (cv : Digest) (xs : List E) (cur : E) (i : ℕ) : E :=
  if i % 4 = 0 then (digestScalars (flScAt τ cv xs (i / 4)).2).1
  else if i % 4 = 1 then (digestScalars (flScAt τ cv xs (i / 4)).2).2
  else if i % 4 = 2 then cur * gen ^ (64 + 2 * (i / 4)) else (flScAt τ cv xs (i / 4)).1

/-- `flock_rounds`: the rows from row 7. -/
def flW2220 (τ : ℕ) (cv : Digest) (xs : List E) (cur : E) : List E :=
  (List.range (4 * τ + 40)).map fun i => if 28 ≤ i ∧ i < 4 * τ + 36 then flRow τ cv xs cur i else 0

/-- The four buffers' words. -/
def flOwn (τ : ℕ) (cv : Digest) (xs : List E) (cur : E) : List (List E) :=
  [flW11 τ cv, flW24 τ cv, flW40 xs, flW2220 τ cv xs cur]

theorem flOwn_fit (τ : ℕ) (cv : Digest) (xs : List E) (cur : E) :
    List.Forall₂ (fun c s => c.length ≤ s) (flOwn τ cv xs cur) (flSizes τ) := by
  simp [flOwn, flSizes, flW11, flW24, flW40, flW2220]

/-- The buffers' bases from `b`. -/
theorem flBases (τ b : ℕ) : bases b (flSizes τ) =
    [b, b + (τ + 14), b + (τ + 14) + (2 * τ + 32), b + (τ + 14) + (2 * τ + 32) + 64] := rfl

section
variable {rd : Reader}

theorem readsAt_get {p : E} {l : List E} (h : ReadsAt rd p l) {k : ℕ} (hk : k < l.length) :
    LoadHolds rd p k (l.getD k 0) := by
  rw [List.getD_eq_getElem _ _ hk]; exact h k hk

/-- **The buffers' words**, read off a memory holding their layout. -/
theorem flBufs_of {τ : ℕ} {cv : Digest} {xs : List E} {cur : E} {b : ℕ}
    (h : MemL rd (bufL b (flSizes τ) (flOwn τ cv xs cur))) :
    FlBufs rd τ cv xs cur (ofK (gpow b)) (ofK (gpow (b + (τ + 14))))
      (ofK (gpow (b + (τ + 14) + (2 * τ + 32)))) (ofK (gpow (b + (τ + 14) + (2 * τ + 32) + 64))) := by
  simp only [bufL, flBases, flOwn, List.zip_cons_cons, List.zip_nil_right] at h
  have h0 := h (b, flW11 τ cv) (by simp)
  have h1 := h (b + (τ + 14), flW24 τ cv) (by simp)
  have h2 := h (b + (τ + 14) + (2 * τ + 32), flW40 xs) (by simp)
  have h3 := h (b + (τ + 14) + (2 * τ + 32) + 64, flW2220 τ cv xs cur) (by simp)
  simp only at h0 h1 h2 h3
  refine ⟨fun j hj => ?_, fun t ht => ⟨?_, ?_⟩, fun i hi => ?_, fun j h7 hj => ⟨?_, ?_, ?_, ?_⟩⟩
  · have := readsAt_get h0 (k := 6 + j) (by simp [flW11]; omega)
    rwa [flW11, getD_map_range _ _ (by omega), ite_neg' (by omega), Nat.add_sub_cancel_left] at this
  · have := readsAt_get h1 (k := 26 + 2 * t) (by simp [flW24]; omega)
    rwa [flW24, getD_map_range _ _ (by omega), ite_pos' (by omega), ite_pos' (by omega),
      show (26 + 2 * t - 26) / 2 = t by omega] at this
  · have := readsAt_get h1 (k := 27 + 2 * t) (by simp [flW24]; omega)
    rwa [flW24, getD_map_range _ _ (by omega), ite_pos' (by omega), ite_neg' (by omega),
      show (27 + 2 * t - 26) / 2 = t by omega] at this
  · have := readsAt_get h2 (k := i) (by simp [flW40]; omega)
    rwa [flW40, getD_map_range _ _ hi] at this
  · have := readsAt_get h3 (k := 4 * j) (by simp [flW2220]; omega)
    rwa [flW2220, getD_map_range _ _ (by omega), ite_pos' (by omega), flRow,
      ite_pos' (by omega), show 4 * j / 4 = j by omega] at this
  · have := readsAt_get h3 (k := 4 * j + 1) (by simp [flW2220]; omega)
    rwa [flW2220, getD_map_range _ _ (by omega), ite_pos' (by omega), flRow,
      ite_neg' (by omega), ite_pos' (by omega), show (4 * j + 1) / 4 = j by omega] at this
  · have := readsAt_get h3 (k := 4 * j + 2) (by simp [flW2220]; omega)
    rwa [flW2220, getD_map_range _ _ (by omega), ite_pos' (by omega), flRow,
      ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega),
      show (4 * j + 2) / 4 = j by omega] at this
  · have := readsAt_get h3 (k := 4 * j + 3) (by simp [flW2220]; omega)
    rwa [flW2220, getD_map_range _ _ (by omega), ite_pos' (by omega), flRow,
      ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
      show (4 * j + 3) / 4 = j by omega] at this

theorem memL_of_agree {rd' : Reader} {L : Main.Layout} (h : MemL rd L)
    (hag : ∀ i, RegionL L i → rd' (gpow i) = rd (gpow i)) : MemL rd' L := by
  intro q hq k hk
  refine ⟨(h q hq k hk).1, ?_⟩
  have := (h q hq k hk).2
  rw [Main.addr_ofK] at this ⊢
  rw [hag (q.1 + k) ⟨q, hq, by omega, by omega⟩]
  exact this

theorem regionL_append {L L' : Main.Layout} {i : ℕ} : RegionL (L ++ L') i ↔ RegionL L i ∨ RegionL L' i := by
  simp only [RegionL]
  constructor
  · rintro ⟨q, hq, h⟩
    rcases List.mem_append.mp hq with hq | hq
    · exact Or.inl ⟨q, hq, h⟩
    · exact Or.inr ⟨q, hq, h⟩
  · rintro (⟨q, hq, h⟩ | ⟨q, hq, h⟩)
    · exact ⟨q, List.mem_append_left _ hq, h⟩
    · exact ⟨q, List.mem_append_right _ hq, h⟩

/-- Words every memory holding `Lin` holds, on a memory agreeing with one of them there. -/
theorem readsAt_transfer {κ : ℕ} {Lin : Main.Layout} {p : E} {xs : List E}
    (hall : ∀ rd, LowDef κ rd → MemL rd Lin → ReadsAt rd p xs) (hlow : LowDef κ rd) (hL : MemL rd Lin)
    {rd' : Reader} (hag : ∀ i, RegionL Lin i → rd' (gpow i) = rd (gpow i)) : ReadsAt rd' p xs :=
  fun k hk => loadHolds_agree hag (hall rd hlow hL k hk) (addr_in_region hall hlow hL hk)

/-- **`verify_flock`'s honest memory** on a memory holding its buffers and the caller's words,
and on any memory agreeing with it there. -/
theorem flMem_of {κ : ℕ} {Lin : Main.Layout} {τ : ℕ} {cv : Digest} {xs chi rcs s : List E}
    {c zc lr zp b : ℕ}
    (hall : ∀ rd, LowDef κ rd → MemL rd Lin →
      ReadsAt rd (ofK (gpow c)) xs ∧ ReadsAt rd (ofK (gpow zc)) chi ∧
        ReadsAt rd (ofK (gpow lr)) rcs ∧ ReadsAt rd (ofK (gpow zp)) s)
    (hlen : xs.length = flLen τ) (hchiE : chi = flChi τ cv xs) (hrcE : rcs = flRc τ cv xs)
    (hsE : s = flS τ xs) (hlow : LowDef κ rd) (hL : MemL rd Lin)
    (hB : MemL rd (bufL b (flSizes τ) (flOwn τ cv xs (ofK (gpow c))))) {rd' : Reader}
    (hag : ∀ i, RegionL (Lin ++ bufL b (flSizes τ) (flOwn τ cv xs (ofK (gpow c)))) i →
      rd' (gpow i) = rd (gpow i)) :
    FlMem rd' τ cv xs (ofK (gpow c)) (ofK (gpow zc)) (ofK (gpow lr)) (ofK (gpow zp))
      (ofK (gpow b)) (ofK (gpow (b + (τ + 14)))) (ofK (gpow (b + (τ + 14) + (2 * τ + 32))))
      (ofK (gpow (b + (τ + 14) + (2 * τ + 32) + 64))) := by
  have hagL : ∀ i, RegionL Lin i → rd' (gpow i) = rd (gpow i) := fun i hi =>
    hag i (regionL_append.mpr (Or.inl hi))
  have hB' := flBufs_of (memL_of_agree hB fun i hi => hag i (regionL_append.mpr (Or.inr hi)))
  have r0 := readsAt_transfer (fun rd h1 h2 => (hall rd h1 h2).1) hlow hL hagL
  have r1 := readsAt_transfer (fun rd h1 h2 => (hall rd h1 h2).2.1) hlow hL hagL
  have r2 := readsAt_transfer (fun rd h1 h2 => (hall rd h1 h2).2.2.1) hlow hL hagL
  have r3 := readsAt_transfer (fun rd h1 h2 => (hall rd h1 h2).2.2.2) hlow hL hagL
  subst hchiE hrcE hsE
  refine ⟨fun k hk => readsAt_get r0 (by omega), hB'.zr, hB'.pts, hB'.p1, hB'.rnd, fun j hj => ?_,
    fun j hj => ?_, fun i hi => ?_⟩
  · have := readsAt_get r1 (k := j) (by simp [flChi]; omega)
    rwa [flChi, getD_map_range _ _ hj] at this
  · have := readsAt_get r2 (k := j) (by simp [flRc]; omega)
    rwa [flRc, getD_map_range _ _ hj] at this
  · have := readsAt_get r3 (k := i) (by simp [flS]; unfold flLen at hlen; omega)
    rwa [flS_getD τ xs hi] at this

/-! ## Where the body loads -/

/-- The body's loads: through which value, at which offsets. -/
def flLoadT : List (ℕ × ℕ × ℕ) :=
  [(2, 0, 78), (2240, 0, 82), (4, 0, 8), (5, 0, 8), (6, 0, 64), (11, 6, 14), (26, 0, 2),
    (37, 0, 2), (40, 0, 64), (2222, 0, 4), (2236, 0, 4)]

def flLoadB (q : V × ℕ) : Bool :=
  flLoadT.any fun t => q.1 == .n t.1 && decide (t.2.1 ≤ q.2) && decide (q.2 < t.2.2)

theorem fl_loads : (flSegs.flatten.filterMap Stmt.loadS).all flLoadB = true := by decide +kernel

theorem addr_gen (a m off : ℕ) :
    (ofK (Parameters.gpow a) * gen ^ m).limb 0 * Parameters.gpow off = Parameters.gpow (a + m + off) := by
  rw [gen_pow_eq_ofK, ← ofK_mul]
  simp [Parameters.gpow, pow_add]

theorem addr_k (a off : ℕ) : (ofK (Parameters.gpow a)).limb 0 * Parameters.gpow off =
    Parameters.gpow (a + off) := Main.addr_ofK a off

theorem region_buf {L : Main.Layout} {a : ℕ} {w : List E} (h : (a, w) ∈ L) {off : ℕ}
    (hoff : off < w.length) : RegionL L (a + off) := ⟨(a, w), h, by simp, by simp; omega⟩

/-! ## The body's shape -/

set_option maxRecDepth 100000 in
theorem fl_not_loop : coreProgram.loop "verify_flock" = false := by
  rw [Program.loop_of_find? find_verify_flock]; decide +kernel

theorem fl_body : Fn.body Data.core12 = flSegs.flatten ++
    [.ret [.n 4369, .n 4370, .n 4373, .n 4374, .n 4375, .n 4376]] := core12_body

theorem fl_straight : flSegs.flatten.all Main.Stmt.straight = true := by decide +kernel

theorem fl_addrs : flSegs.flatten.filterMap Main.Stmt.addrS = [] := by decide +kernel

theorem fl_allocs : flSegs.flatten.filterMap Main.Stmt.allocSz =
    [(.n 11, .inr (.n 10)), (.n 24, .inr (.n 23)), (.n 40, .inl 64), (.n 2220, .inr (.n 2219))] := by
  decide +kernel

theorem fl_calls : flSegs.flatten.filterMap Main.Stmt.callS =
    [(some (.n 30), "__loop81", [.n 31, .n 33, .n 24, .n 11], []),
      (some (.n 2228), "__loop82", [.n 2229, .n 2231, .n 2220, .n 11, .n 4], [])] := by
  decide +kernel

theorem pure81 : coreProgram.PureIn ["__loop81"] := by
  intro g hg fn hfn
  simp only [List.mem_singleton] at hg
  subst hg
  rw [find_loop81] at hfn; cases hfn; rw [core140_body]; decide +kernel

theorem pure82 : coreProgram.PureIn ["__loop82"] := by
  intro g hg fn hfn
  simp only [List.mem_singleton] at hg
  subst hg
  rw [find_loop82] at hfn; cases hfn; rw [core141_body]; decide +kernel

theorem word_gm6 : word 2017612633061982209 0 0 * gen ^ 6 = 1 := by
  rw [word_eOfNat, gen_pow_eq_ofK]
  show ofK (K.ofBits 2017612633061982209) * ofK (Parameters.gpow 6) = 1
  rw [← ofK_mul, show K.ofBits 2017612633061982209 * Parameters.gpow 6 = 1 by decide +kernel, ofK_one]

theorem fl_v1851 (τ : ℕ) :
    gen ^ τ * word 16384 0 0 * word 2017612633061982209 0 0 = gen ^ (τ + 8) := by
  rw [word_g14, show gen ^ τ * gen ^ 14 = gen ^ (τ + 8) * gen ^ 6 by rw [← pow_add, ← pow_add],
    mul_assoc, mul_comm (gen ^ 6), word_gm6, mul_one]

/-! ## `verify_flock`, placed -/

/-- The two loops' frames: on the caller's words and `verify_flock`'s buffers from `b`. -/
def flKids (τ : ℕ) (cv : Digest) (xs : List E) (cur zchis : E) (Lin : Main.Layout) (b : ℕ) :
    List Kid :=
  [⟨"__loop81", true, [word 8192 0 0, gen ^ τ * word 16384 0 0, ofK (Parameters.gpow (b + (τ + 14))),
      ofK (Parameters.gpow b)], Lin ++ bufL b (flSizes τ) (flOwn τ cv xs cur), Returns []⟩,
    ⟨"__loop82", true, [word 128 0 0, gen ^ τ * word 256 0 0,
      ofK (Parameters.gpow (b + (τ + 14) + (2 * τ + 32) + 64)), ofK (Parameters.gpow b), zchis],
      Lin ++ bufL b (flSizes τ) (flOwn τ cv xs cur), Returns []⟩]

theorem logG_g (e : ℕ) (he : e < 2 ^ 64 - 1) : logG (gen ^ e) = e := by
  rw [gen_pow_eq_ofK]; exact logG_spec he

end

end
end LeanVM.Guest.B1
