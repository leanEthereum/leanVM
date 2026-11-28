/-
  LeanVM.Guest.B1.VsC.RstLoopA

  `ring_switch_target`'s loop completes with no words of its own, and every valid tree of it has
  its shape.
-/

module

public import LeanVM.Guest.B1.VsC.LoopFlat
public import LeanVM.Guest.B1.VsC.LrC
public import LeanVM.Guest.B1.Ring.Target
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«ring_switch_target_loop0»

/-!
# `ring_switch_target_loop0`, complete

Iteration `j < 8` (`x = g^j`) reads the challenges `g_0 .. g_7` at `map_challenges[8 ..]`, the
eight slices at `slices·g^(8j)`, row `j` of the eight Horner chains at `rs_chain·g^(8j)`, and stores
row `j + 1` past it. The honest chain words `rsChain s G`: row `j`, chain `p`, is the Horner sum
in `w_p` of the images `Ψ(s_i)` of the first `8 j` slices (`rstH`).

Each iteration is evaluated forward (`fwdVal`) on the memory: its atoms need no side condition or
load through a pointer `rlChecks` names (the challenges, the iteration's slices and chain row), but
for its eight stores, whose words are the next row (the guest stream's `holds_psRowAt`, `hz_steps`).

* `rl_loop`: the loop completes from iteration `j`, with no words of its own.
* `rl_shape`: every valid tree of it from iteration `j` has block `lpB`, ends at its cursor, and
  loads from the region holding the arrays.
-/

namespace LeanVM.Guest.B1.VsC

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Memory LeanVM.Guest.B1
open LeanVM.Guest.Complete LeanVM.Guest.B1.Fwd LeanVM.Guest.Value LeanVM.Guest.B1.VerifySub
open LeanVM.Protocol.Verifier LeanVM.Guest.B1.Whir

@[expose] public section

/-! ## The honest chain -/

/-- Slice `i`'s image `Ψ(s_i)` under the challenges `G`. -/
def rsImg (s G : List E) (i : ℕ) : E := ringPsi (s.getD i 0) G

/-- Row `j`, chain `p`: the Horner sum in `w_p` of the first `8 j` images. -/
def rstH (s G : List E) (j p : ℕ) : E :=
  ((List.range (8 * j)).map (rsImg s G)).foldl (hstep (ofK (ringWK.getD p 0))) 0

/-- `rs_chain`'s honest words: nine rows of eight chains. -/
def rsChain (s G : List E) : List E := (List.range 72).map fun i => rstH s G (i / 8) (i % 8)

theorem rsChain_load {rd : Reader} {s G : List E} {a : ℕ} (h : ReadsAt rd (ptrAt a) (rsChain s G))
    {j p : ℕ} (hj : j ≤ 8) (hp : p < 8) : LoadHolds rd (ptrAt a) (8 * j + p) (rstH s G j p) := by
  have := h (8 * j + p) (by simp [rsChain]; omega)
  simp only [rsChain, List.getElem_map, List.getElem_range] at this
  rwa [show (8 * j + p) / 8 = j by omega, show (8 * j + p) % 8 = p by omega] at this

theorem rsH_succ (s G : List E) (j p : ℕ) :
    ((List.range 8).map fun r => rsImg s G (8 * j + r)).foldl (hstep (ofK (ringWK.getD p 0))) (rstH s G j p) =
      rstH s G (j + 1) p := by
  simp only [rstH]
  rw [show 8 * (j + 1) = 8 * j + 8 by ring, List.range_add, List.map_append, List.foldl_append, List.map_map]
  rfl

/-! ## The iteration's shape facts -/

/-- The loop's name. -/
abbrev rlName : String := name% «ring_switch_target_loop0»

abbrev rlRows : ℕ := val% «ring_switch_target_loop0» "rows"
abbrev rlRow : ℕ := val% «ring_switch_target_loop0» "row"
abbrev rlGuard : ℕ := val% «ring_switch_target_loop0» "s8#3"

/-- The loop body before its tail call. -/
def rlL : List Stmt :=
  ((List.range 8).map fun b ↦ [.atom (.load (.n ((val% «ring_switch_target_loop0» "g[0]") + b)) (.n (val% «ring_switch_target_loop0» "map_challenges")) (8 + b))]).flatten ++
  [.atom (.mul (.n (val% «ring_switch_target_loop0» "rows~0")) (.n (val% «ring_switch_target_loop0» "x_round")) (.n (val% «ring_switch_target_loop0» "x_round"))), .atom (.mul (.n (val% «ring_switch_target_loop0» "rows~1")) (.n (val% «ring_switch_target_loop0» "rows~0")) (.n (val% «ring_switch_target_loop0» "rows~0"))),
    .atom (.mul (.n (val% «ring_switch_target_loop0» "rows~2")) (.n (val% «ring_switch_target_loop0» "rows~1")) (.n (val% «ring_switch_target_loop0» "rows~1"))), .atom (.mul (.n (val% «ring_switch_target_loop0» "rows")) (.n (val% «ring_switch_target_loop0» "slices")) (.n (val% «ring_switch_target_loop0» "rows~2")))] ++
  ((List.range 8).map psRow).flatten ++
  [.atom (.mul (.n (val% «ring_switch_target_loop0» "row~0")) (.n (val% «ring_switch_target_loop0» "x_round")) (.n (val% «ring_switch_target_loop0» "x_round"))), .atom (.mul (.n (val% «ring_switch_target_loop0» "row~1")) (.n (val% «ring_switch_target_loop0» "row~0")) (.n (val% «ring_switch_target_loop0» "row~0"))),
    .atom (.mul (.n (val% «ring_switch_target_loop0» "row~2")) (.n (val% «ring_switch_target_loop0» "row~1")) (.n (val% «ring_switch_target_loop0» "row~1"))), .atom (.mul (.n (val% «ring_switch_target_loop0» "row")) (.n (val% «ring_switch_target_loop0» "rs_chain")) (.n (val% «ring_switch_target_loop0» "row~2")))] ++
  ((List.range 8).map hzRow).flatten ++
  [.atom (.const (.n (val% «ring_switch_target_loop0» "s8#0")) (word 2 0)), .atom (.mul (.n (val% «ring_switch_target_loop0» "s8#1")) (.n (val% «ring_switch_target_loop0» "x_round")) (.n (val% «ring_switch_target_loop0» "s8#0"))),
    .atom (.const (.n (val% «ring_switch_target_loop0» "s8#2")) (word 256 0)), .atom (.add (.n (val% «ring_switch_target_loop0» "s8#3")) (.n (val% «ring_switch_target_loop0» "s8#1")) (.n (val% «ring_switch_target_loop0» "s8#2"))),
    .atom (.const (.n (val% «ring_switch_target_loop0» "s8#4")) (word 2 0)), .atom (.mul (.n (val% «ring_switch_target_loop0» "s8#5")) (.n (val% «ring_switch_target_loop0» "x_round")) (.n (val% «ring_switch_target_loop0» "s8#4")))]

/-- The tail call's arguments. -/
abbrev rlT : List V :=
  [.n (val% «ring_switch_target_loop0» "s8#5"), .n (val% «ring_switch_target_loop0» "map_challenges"),
    .n (val% «ring_switch_target_loop0» "slices"), .n (val% «ring_switch_target_loop0» "rs_chain")]

/-- The stores: chain `p`'s next entry. -/
def rlStores : List Atom := (List.range 8).map fun p => .load (.n (hzBase p + 24)) (.n rlRow) (8 + p)

/-- The pointers: the challenges, the iteration's slices, its chain rows. -/
def rlPs : List (ℕ × ℕ) := [(1, 16), (rlRows, 8), (rlRow, 16)]

/-- What the kernel checks of the loop. -/
def rlChecks : Bool :=
  (chk 4 loop13T).isSome && decide (storesOf 4 loop13T = rlStores) && rlL.all Stmt.isAtom &&
    (atomsOf rlL).all (loadOkB rlPs) &&
    (List.range 8).all (fun r => (atomsOf (psRow r)).all fun a => decide (a ∉ rlStores)) &&
    (List.range 8).all (fun p => decide (Atom.load (.n (hzBase p)) (.n rlRow) p ∉ rlStores))

set_option maxRecDepth 100000 in
theorem rlChecks_ok : rlChecks = true := by decide +kernel

theorem loop13T_split : loop13T = ((atomsOf rlL).map Stmt.atom ++ [Stmt.callIf (.n rlGuard) rlName rlT]) ++ [.ret []] := by
  have hat : rlL.all Stmt.isAtom = true := by
    have := rlChecks_ok; simp only [rlChecks, Bool.and_eq_true] at this; exact this.1.1.1.2
  rw [← eq_map_atomsOf (allAtoms_of_isAtom hat), loop13T, rlL]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem rl_psRow_ns {r : ℕ} (hr : r < 8) {a : Atom} (ha : Stmt.atom a ∈ psRow r) : a ∉ rlStores := by
  have := rlChecks_ok
  simp only [rlChecks, Bool.and_eq_true] at this
  have h := List.all_eq_true.mp this.1.2 r (List.mem_range.mpr hr)
  simpa using List.all_eq_true.mp h a (mem_atomsOf' ha)

theorem rl_hzLoad_ns {p : ℕ} (hp : p < 8) : Atom.load (.n (hzBase p)) (.n rlRow) p ∉ rlStores := by
  have := rlChecks_ok
  simp only [rlChecks, Bool.and_eq_true] at this
  simpa using List.all_eq_true.mp this.2 p (List.mem_range.mpr hp)

theorem rl_params : (fn% «ring_switch_target_loop0»).params = (List.range 4).map V.n := rfl


theorem rl_body : (fn% «ring_switch_target_loop0»).body =
    ((atomsOf rlL).map Stmt.atom ++ [Stmt.callIf (.n rlGuard) rlName rlT]) ++ [.ret []] := by
  rw [loop13_body, loop13T_split]

/-- The loop's arguments at iteration `j`. -/
def rlArgs (j im isl ic : ℕ) : List E := [gen ^ j, ptrAt im, ptrAt isl, ptrAt ic]

/-- What the loop reads: the challenges, the slices, the chain. -/
def RlMem (im isl ic : ℕ) (s ch : List E) (rd : Reader) : Prop :=
  ReadsAt rd (ptrAt im) ch ∧ ReadsAt rd (ptrAt isl) s ∧ ReadsAt rd (ptrAt ic) (rsChain s (ch.drop 8))

/-- `rlL`'s third and fifth chunks. -/
theorem rlL_psRow {r : ℕ} (hr : r < 8) {x : Stmt} (h : x ∈ psRow r) : x ∈ rlL := by
  unfold rlL; simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inr (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨r, List.mem_range.mpr hr, rfl⟩, h⟩))))

theorem rlL_hzRow {p : ℕ} (hp : p < 8) {x : Stmt} (h : x ∈ hzRow p) : x ∈ rlL := by
  unfold rlL; simp only [List.mem_append]
  exact Or.inl (Or.inr (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨p, List.mem_range.mpr hp, rfl⟩, h⟩))

theorem rlL_g {b : ℕ} (hb : b < 8) :
    Stmt.atom (.load (.n ((val% «ring_switch_target_loop0» "g[0]") + b)) (.n (val% «ring_switch_target_loop0» "map_challenges")) (8 + b)) ∈ rlL := by
  unfold rlL; simp only [List.mem_append]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨b, List.mem_range.mpr hb, rfl⟩,
    List.mem_singleton_self _⟩)))))

theorem hzStep_mem {a p r : ℕ} (hr : r < 8) {x : Stmt} (h : x ∈ hzStep a p r) : x ∈ hzRowAt a p := by
  unfold hzRowAt; simp only [List.mem_append]
  exact Or.inl (Or.inr (List.mem_flatten.mpr ⟨_, List.mem_map.mpr ⟨r, List.mem_range.mpr hr, rfl⟩, h⟩))

/-- The values every iteration's atoms pin: the pointers, the guard and the tail call's arguments. -/
theorem rl_vals {rd : Reader} {σ : Val} {j im isl ic : ℕ}
    (hp : ∀ i < 4, σ (.n i) = (rlArgs j im isl ic).getD i 0)
    (hA : ∀ a, Stmt.atom a ∈ rlL → needsSide a = false → a.Holds rd σ) :
    σ (.n 1) = ptrAt im ∧ σ (.n rlRows) = ptrAt (isl + 8 * j) ∧ σ (.n rlRow) = ptrAt (ic + 8 * j) ∧
      σ (.n rlGuard) = gen ^ (j + 1) + gen ^ 8 ∧ rlT.map σ = rlArgs (j + 1) im isl ic := by
  have p0 : σ (.n 0) = gen ^ j := hp 0 (by decide)
  have p1 : σ (.n 1) = ptrAt im := hp 1 (by decide)
  have p2 : σ (.n 2) = ptrAt isl := hp 2 (by decide)
  have p3 : σ (.n 3) = ptrAt ic := hp 3 (by decide)
  have e0 := hA (.mul (.n (val% «ring_switch_target_loop0» "rows~0")) (.n (val% «ring_switch_target_loop0» "x_round"))
    (.n (val% «ring_switch_target_loop0» "x_round"))) (by simp [rlL]) rfl
  have e1 := hA (.mul (.n (val% «ring_switch_target_loop0» "rows~1")) (.n (val% «ring_switch_target_loop0» "rows~0"))
    (.n (val% «ring_switch_target_loop0» "rows~0"))) (by simp [rlL]) rfl
  have e2 := hA (.mul (.n (val% «ring_switch_target_loop0» "rows~2")) (.n (val% «ring_switch_target_loop0» "rows~1"))
    (.n (val% «ring_switch_target_loop0» "rows~1"))) (by simp [rlL]) rfl
  have e3 := hA (.mul (.n rlRows) (.n (val% «ring_switch_target_loop0» "slices"))
    (.n (val% «ring_switch_target_loop0» "rows~2"))) (by simp [rlL]) rfl
  have f0 := hA (.mul (.n (val% «ring_switch_target_loop0» "row~0")) (.n (val% «ring_switch_target_loop0» "x_round"))
    (.n (val% «ring_switch_target_loop0» "x_round"))) (by simp [rlL]) rfl
  have f1 := hA (.mul (.n (val% «ring_switch_target_loop0» "row~1")) (.n (val% «ring_switch_target_loop0» "row~0"))
    (.n (val% «ring_switch_target_loop0» "row~0"))) (by simp [rlL]) rfl
  have f2 := hA (.mul (.n (val% «ring_switch_target_loop0» "row~2")) (.n (val% «ring_switch_target_loop0» "row~1"))
    (.n (val% «ring_switch_target_loop0» "row~1"))) (by simp [rlL]) rfl
  have f3 := hA (.mul (.n rlRow) (.n (val% «ring_switch_target_loop0» "rs_chain"))
    (.n (val% «ring_switch_target_loop0» "row~2"))) (by simp [rlL]) rfl
  have g0 := hA (.const (.n (val% «ring_switch_target_loop0» "s8#0")) (word 2 0)) (by simp [rlL]) rfl
  have g1 := hA (.mul (.n (val% «ring_switch_target_loop0» "s8#1")) (.n (val% «ring_switch_target_loop0» "x_round"))
    (.n (val% «ring_switch_target_loop0» "s8#0"))) (by simp [rlL]) rfl
  have g2 := hA (.const (.n (val% «ring_switch_target_loop0» "s8#2")) (word 256 0)) (by simp [rlL]) rfl
  have g3 := hA (.add (.n (val% «ring_switch_target_loop0» "s8#3")) (.n (val% «ring_switch_target_loop0» "s8#1"))
    (.n (val% «ring_switch_target_loop0» "s8#2"))) (by simp [rlL]) rfl
  have g4 := hA (.const (.n (val% «ring_switch_target_loop0» "s8#4")) (word 2 0)) (by simp [rlL]) rfl
  have g5 := hA (.mul (.n (val% «ring_switch_target_loop0» "s8#5")) (.n (val% «ring_switch_target_loop0» "x_round"))
    (.n (val% «ring_switch_target_loop0» "s8#4"))) (by simp [rlL]) rfl
  simp only [Atom.Holds] at e0 e1 e2 e3 f0 f1 f2 f3 g0 g1 g2 g3 g4 g5
  have x8 : (gen ^ j * gen ^ j) * (gen ^ j * gen ^ j) * ((gen ^ j * gen ^ j) * (gen ^ j * gen ^ j)) =
      gen ^ (8 * j) := by ring
  refine ⟨p1, by rw [e3, e2, e1, e0, p0, p2, x8, ptrAt_mul_gen], by rw [f3, f2, f1, f0, p0, p3, x8, ptrAt_mul_gen],
    by rw [g3, g1, g2, g0, p0, word_gen, ← word_two_pow (by decide : 8 < 64), pow_succ]; rfl, ?_⟩
  simp only [rlT, List.map_cons, List.map_nil, g5, g4, p0, p1, p2, p3, rlArgs, word_gen, pow_succ]

variable {kd : ℕ}

/-- **Iteration `j` of the loop completes**, from the next one's. -/
theorem rl_step {im isl ic : ℕ} {s ch : List E} (hs : s.length = 64) (hch : ch.length = 16) {j : ℕ} (hj : j < 8)
    (hnext : j + 1 < 8 → CallCompletes0 kd rlName (rlArgs (j + 1) im isl ic) [] (RlMem im isl ic s ch) PostQuiet) :
    CallCompletes0 kd rlName (rlArgs j im isl ic) [] (RlMem im isl ic s ch) PostQuiet := by
  have hck := rlChecks_ok
  simp only [rlChecks, Bool.and_eq_true, decide_eq_true_eq] at hck
  obtain ⟨⟨⟨⟨⟨hc, hst⟩, -⟩, hok⟩, -⟩, -⟩ := hck
  obtain ⟨c', hc⟩ := Option.isSome_iff_exists.mp hc
  set args := rlArgs j im isl ic with hargs
  have hchk : chk args.length (fn% «ring_switch_target_loop0»).body = some c' := by rw [loop13_body]; exact hc
  refine callCompletes0_loopFlat find_loop13 rl_body (by rw [rl_params]; rfl) hok
    (fun rd => fwdVal rd (fun _ => 0) args (fn% «ring_switch_target_loop0»).body) fun rd hl hP => ?_
  set σ := fwdVal rd (fun _ => 0) args (fn% «ring_switch_target_loop0»).body with hσ
  obtain ⟨hmc, hsl, hcw⟩ := hP
  have hmem : ∀ a, Stmt.atom a ∈ rlL → Stmt.atom a ∈ (fn% «ring_switch_target_loop0»).body := fun a ha => by
    rw [rl_body]
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨a, mem_atomsOf' ha, rfl⟩))
  have hNS : ∀ a, Stmt.atom a ∈ rlL → needsSide a = false → a.Holds rd σ :=
    fun a ha hn => fwd_holds_noSide hchk (hmem a ha) hn
  have hp : ∀ i < 4, σ (.n i) = args.getD i 0 := fun i hi => fwd_param hchk (by simpa [hargs, rlArgs] using hi)
  have p0 : σ (.n 0) = gen ^ j := hp 0 (by decide)
  have p1 : σ (.n 1) = ptrAt im := hp 1 (by decide)
  have p2 : σ (.n 2) = ptrAt isl := hp 2 (by decide)
  have p3 : σ (.n 3) = ptrAt ic := hp 3 (by decide)
  obtain ⟨-, vRows, vRow, vg, vt⟩ := rl_vals hp hNS
  have hbase : ∀ q ∈ rlPs, ∃ a, σ (.n q.1) = ptrAt a ∧ ∀ o < q.2, ∃ v, LoadHolds rd (ptrAt a) o v := by
    intro q hq
    simp only [rlPs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact ⟨im, p1, fun o ho => ⟨_, hmc o (by simp only at ho; omega)⟩⟩
    · exact ⟨isl + 8 * j, vRows, fun o ho => ⟨_, readsAt_off hsl (by simp only at ho; omega)⟩⟩
    · exact ⟨ic + 8 * j, vRow, fun o ho => ⟨_, readsAt_off hcw (by simp only at ho; simp [rsChain]; omega)⟩⟩
  -- every atom but the stores
  have hP1 : ∀ a, Stmt.atom a ∈ rlL → a ∉ rlStores → a.Holds rd σ := by
    intro a ha hS
    cases hn : needsSide a
    · exact hNS a ha hn
    · have hk := List.all_eq_true.mp hok a (mem_atomsOf' ha)
      cases a with
      | load d p off =>
        refine fwd_holds_load hchk (hmem _ ha) ?_ (loadHolds_of_loadOk hbase hk)
        show Atom.load d p off ∉ storesOf 4 (fn% «ring_switch_target_loop0»).body
        rw [loop13_body, hst]; exact hS
      | _ => simp [loadOkB, hn] at hk
  -- the challenges
  have hG : gVals σ = ch.drop 8 := by
    refine List.ext_getElem (by simp [gVals, hch]) fun b h1 h2 => ?_
    have hb : b < 8 := by simpa [gVals] using h1
    have l := hP1 _ (rlL_g hb) (by simp [rlStores])
    simp only [Atom.Holds, p1] at l
    simp only [gVals, List.getElem_map, List.getElem_range, List.getElem_drop]
    exact loadHolds_unique l (hmc _ (by omega))
  -- the images
  have hrow : ∀ r < 8, σ (.n (psBase r)) = s.getD (8 * j + r) 0 ∧
      σ (.n (psBase r + 22)) = rsImg s (ch.drop 8) (8 * j + r) := by
    intro r hr
    have hh : Stmt.HoldsList (fun _ _ _ => True) rd σ (psRow r) True (fun _ => True) :=
      (holdsList_atoms (fun st hst => by
        unfold psRow psRowAt at hst
        simp only [List.mem_append, List.mem_cons, List.mem_flatten, List.mem_map, List.mem_range,
          List.not_mem_nil, or_false] at hst
        rcases hst with (rfl | rfl | rfl | rfl | rfl) | ⟨l, ⟨k, -, rfl⟩, hl⟩
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
        simp only [psStage, List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl | rfl <;> exact ⟨_, rfl⟩) True _).mpr
        ⟨fun a ha => hP1 a (rlL_psRow hr ha) (rl_psRow_ns hr ha), trivial⟩
    obtain ⟨l0, e22⟩ := holds_psRowAt hh
    rw [vRows] at l0
    have hv : σ (.n (psBase r)) = s.getD (8 * j + r) 0 := by
      rw [loadHolds_unique l0 (readsAt_off hsl (by omega)), List.getD_eq_getElem _ _ (by omega)]
    exact ⟨hv, by rw [e22, hv, hG]; rfl⟩
  have hps : psVals σ = (List.range 8).map fun r => rsImg s (ch.drop 8) (8 * j + r) :=
    List.map_congr_left fun r hr => (hrow r (List.mem_range.mp hr)).2
  -- the chains
  have hnew : ∀ p < 8, σ (.n (hzBase p + 24)) = rstH s (ch.drop 8) (j + 1) p := by
    intro p hp
    have hz := hz_steps (σ := σ) (a := hzBase p) hp (fun r hr => by
      have hm : ∀ x ∈ hzStep (hzBase p) p r, x ∈ rlL := fun x hx => rlL_hzRow hp (hzStep_mem hr hx)
      exact ⟨hNS (.const (.n (hzBase p + 1 + 3 * r)) (word (ringWNat.getD p 0) 0)) (hm _ (by simp [hzStep])) rfl,
        hNS (.mul (.n (hzBase p + 2 + 3 * r)) (.n (hzBase p + 3 * r)) (.n (hzBase p + 1 + 3 * r)))
          (hm _ (by simp [hzStep])) (by simp [needsSide]),
        hNS (.add (.n (hzBase p + 3 + 3 * r)) (.n (hzBase p + 2 + 3 * r)) (.n (psBase r + 22)))
          (hm _ (by simp [hzStep])) rfl⟩) 8 le_rfl
    have l0 := hP1 (.load (.n (hzBase p)) (.n rlRow) p) (rlL_hzRow hp (by simp [hzRow, hzRowAt])) (rl_hzLoad_ns hp)
    simp only [Atom.Holds, vRow] at l0
    have hv := loadHolds_unique l0 (by
      have := rsChain_load hcw (j := j) (by omega) hp
      rwa [← loadHolds_ptrAt_add] at this)
    rw [show hzBase p + 24 = hzBase p + 3 * 8 by ring, hz, ← psVals, hps, hv, rsH_succ]
  refine ⟨by rw [rl_params]; exact fwd_params hchk, fun a ha => ?_, ?_, fun hz => ?_⟩
  · have ha' := mem_of_mem_atomsOf ha
    by_cases hS : a ∈ rlStores
    · simp only [rlStores, List.mem_map, List.mem_range] at hS
      obtain ⟨p, hp, rfl⟩ := hS
      show LoadHolds rd (σ (.n rlRow)) (8 + p) (σ (.n (hzBase p + 24)))
      rw [vRow, hnew p hp, loadHolds_ptrAt_add, show 8 * j + (8 + p) = 8 * (j + 1) + p by ring]
      exact rsChain_load hcw (by omega) hp
    · exact hP1 a ha' hS
  · rw [vg]; exact isInK_add (gen_pow_isInK _) (gen_pow_isInK _)
  · have hne : j + 1 ≠ 8 := fun h => hz (by rw [vg, h]; exact CharTwo.add_self_eq_zero _)
    obtain ⟨t, hn, hv2, hb2, hq2⟩ := hnext (by omega) rd hl ⟨hmc, hsl, hcw⟩
    exact ⟨t, hn, by rw [vt]; exact hv2, hb2, hq2⟩

/-- **The loop completes from iteration `j`**, every `j < 8`. -/
theorem rl_loop {im isl ic : ℕ} {s ch : List E} (hs : s.length = 64) (hch : ch.length = 16) :
    ∀ m j, 8 = j + m + 1 →
      CallCompletes0 kd rlName (rlArgs j im isl ic) [] (RlMem im isl ic s ch) PostQuiet := by
  intro m
  induction m with
  | zero => intro j hj; exact rl_step hs hch (by omega) (fun h => absurd h (by omega))
  | succ m IH => intro j hj; exact rl_step hs hch (by omega) (fun _ => IH (j + 1) (by omega))


/-! ## Shapes -/

/-- What the loop loads from: the challenges, the slices, the chain. -/
def RlRegion (im isl ic : ℕ) (R : ℕ → Prop) : Prop :=
  (∀ i < 16, R (im + i)) ∧ (∀ i < 64, R (isl + i)) ∧ ∀ i < 72, R (ic + i)

theorem rl_loopB : coreProgram.loop rlName = true := by
  rw [Program.loop_of_find? find_loop13, Fn.loop, rl_body]
  simp [List.reverse_append]
  rfl

/-- **Every valid tree of the loop from iteration `j < 8` has its shape.** -/
theorem rl_shape {fs : String → ℕ} {al : String → Bool} {im isl ic : ℕ} {R : ℕ → Prop}
    (hR : RlRegion im isl ic R) :
    ∀ m j, 8 = j + m + 1 → ∀ rd t, t.name = rlName →
      t.Valid coreProgram rd (rlArgs j im isl ic) [] → t.BufsOk coreProgram →
      ShapeR fs al (lpB fs rlName 8 j) _root_.id R t := by
  have hck := rlChecks_ok
  simp only [rlChecks, Bool.and_eq_true] at hck
  obtain ⟨⟨⟨⟨-, -⟩, hok⟩, -⟩, -⟩ := hck
  have hbase : ∀ j, j < 8 → ∀ rd σ, (fn% «ring_switch_target_loop0»).params.map σ = rlArgs j im isl ic →
      (∀ a ∈ atomsOf rlL, a.Holds rd σ) →
      (∀ q ∈ rlPs, ∃ b, σ (.n q.1) = ptrAt b ∧ ∀ o < q.2, R (b + o)) ∧
        σ (.n rlGuard) = gen ^ (j + 1) + gen ^ 8 ∧ rlT.map σ = rlArgs (j + 1) im isl ic := by
    intro j hj rd σ hp hA
    have hp' : ∀ i < 4, σ (.n i) = (rlArgs j im isl ic).getD i 0 := fun i hi => by
      rw [← hp, rl_params]; simp [List.getD_eq_getElem?_getD, hi]
    obtain ⟨v1, vR, vW, vg, vt⟩ := rl_vals hp' fun a ha _ => hA a (mem_atomsOf' ha)
    refine ⟨fun q hq => ?_, vg, vt⟩
    simp only [rlPs, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl
    · exact ⟨im, v1, fun o ho => hR.1 o ho⟩
    · exact ⟨isl + 8 * j, vR, fun o ho => by rw [Nat.add_assoc]; exact hR.2.1 _ (by simp only at ho; omega)⟩
    · exact ⟨ic + 8 * j, vW, fun o ho => by rw [Nat.add_assoc]; exact hR.2.2 _ (by simp only at ho; omega)⟩
  have e : ∀ j, j < 8 → fs rlName + lpB fs rlName 8 (j + 1) = lpB fs rlName 8 j := fun j hj => by
    simp only [lpB]; rw [show 8 - j = (8 - (j + 1)) + 1 by omega]; ring
  intro m
  induction m with
  | zero =>
    intro j hj rd t hn hv hbt
    have h := shapeR_loopFlat (fs := fs) (al := al) (args := rlArgs j im isl ic) (R := R)
      (Bt := lpB fs rlName 8 (j + 1)) find_loop13 rl_body rl_loopB hok ?_ rd t hn hv hbt
    · rwa [e j (by omega)] at h
    · intro rd' σ hp hA
      obtain ⟨hb, vg, -⟩ := hbase j (by omega) rd' σ hp hA
      refine ⟨hb, fun _ => by simp only [lpB]; rw [show 8 - (j + 1) = 0 by omega]; ring, fun hz => ?_⟩
      exact absurd (by rw [vg, show j + 1 = 8 by omega]; exact CharTwo.add_self_eq_zero _) hz
  | succ m IH =>
    intro j hj rd t hn hv hbt
    have h := shapeR_loopFlat (fs := fs) (al := al) (args := rlArgs j im isl ic) (R := R)
      (Bt := lpB fs rlName 8 (j + 1)) find_loop13 rl_body rl_loopB hok ?_ rd t hn hv hbt
    · rwa [e j (by omega)] at h
    · intro rd' σ hp hA
      obtain ⟨hb, vg, vt⟩ := hbase j (by omega) rd' σ hp hA
      refine ⟨hb, fun hz => absurd hz ?_, fun _ t' hn' hv' hb'' => ?_⟩
      · rw [vg]; exact (gen_add_ne' (by omega) (by omega)).not.mpr (by omega)
      · rw [vt] at hv'
        exact IH (j + 1) (by omega) rd' t' hn' hv' hb''

theorem rl_pure : coreProgram.PureIn [rlName] := by
  intro g hg fn' hf'
  rw [List.mem_singleton] at hg
  subst hg
  rw [find_loop13, Option.some.injEq] at hf'
  subst hf'
  rw [loop13_body]
  decide +kernel

/-- **The loop completes placed** from its first iteration, with no words of its own, ending at its
cursor. -/
theorem rl_placed {fs : String → ℕ} {al : String → Bool} {cert : String → V → ℕ} {k im isl ic : ℕ}
    {s ch : List E} (hs : s.length = 64) (hch : ch.length = 16) {R : ℕ → Prop} (hR : RlRegion im isl ic R)
    (fp c : ℕ) :
    CallAtA fs al cert k rlName (rlArgs 0 im isl ic) [] R (fun _ => False) (fun _ => True) (RlMem im isl ic s ch)
      PostQuiet (lpB fs rlName 8 0) fp c c :=
  callAtA_of_callCompletes0 rl_pure (List.mem_singleton_self _) le_rfl (rl_loop hs hch 7 0 rfl)
    fun rd t _ _ hn hv hb _ =>
      let h := rl_shape (fs := fs) (al := al) hR 7 0 rfl rd t hn hv hb
      ⟨h.1, h.2.1 c, h.2.2.1, h.2.2.2⟩

end
end LeanVM.Guest.B1.VsC
