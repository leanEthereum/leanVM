/-
  LeanVM.Guest.B1.Digest.ChildListAt

  `child_claim_list_any` in the uniform placed form, by a tree of honest shape, within bounds
  before the memory: its chain buffer after its frame, holding the sponge states an honest run
  leaves, its callees after it; it reads the records' marks and cells among its caller's words.
-/

module

public import LeanVM.Guest.B1.Digest.ChildListAt0
public import LeanVM.Guest.B1.Main.NodeHonestAt
public import LeanVM.Guest.Data.NameStrings

/-!
# The walk by hinted indices, placed

`child_claim_list_any_completeAtTB`: for `n = 136a + 17b + c < 136 · 2^20` honest records
(`RecMem`: slots `o j` below `L`, marks `base · g^j` at `region · g^(o j)`, cells at
`entries · g^(4 o j)`) among the caller's words, with `L ≤ 2^κ` (the range checks read below
`2^κ`), `child_claim_list_any` on `[g^eP, g^rg, base, g^L, g^a, g^b, g^c]` is complete returning
the cells' digest: its chain buffer (`chainCells`, `13 (a + b + 1)` words) after its frame, then
`child_claim_list_any_loop0` over the `a` big frames, `child_claim_list_any_loop1` over the `b`
groups (`anyLoop_completeAtB`), `child_claim_list_last__L{c}` (`ccl_completeAtB`); by a tree of
honest shape `anyHonest n` (`anyQ`, `anyCalls`, `anyBufs`), within `anyB fs n` words.
`_completeAtT`, `_completeAt`: the same, forgetting the bound.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDT CompleteAtDTB KidsDTB kidsFromInT_of_kidsDTB
  kidsBoundL Returns Kid DisjL Within disj_append regionsOk_of within_append LowDef)
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append)
open LeanVM.Guest.B1.Da (SlOk slEvs_holds exists_of_length_succ limb0_gen_pow_mul reads_of_memL
  regionL_of_mem)
open LeanVM.Guest.Budget (NodeHonest)

@[expose] public section

theorem regionL_append_left {L L' : Main.Layout} {i : ℕ} (h : RegionL L i) : RegionL (L ++ L') i :=
  let ⟨q, hq, h1, h2⟩ := h; ⟨q, List.mem_append_left _ hq, h1, h2⟩

theorem regionL_append_right {L L' : Main.Layout} {i : ℕ} (h : RegionL L' i) : RegionL (L ++ L') i :=
  let ⟨q, hq, h1, h2⟩ := h; ⟨q, List.mem_append_right _ hq, h1, h2⟩

/-! ## The honest shape -/

/-- `child_claim_list_any`'s words that end its loops and size its buffer (`n = 136a + 17b + c`):
`g^a`, `g^b`, `g^c` at `v4`, `v5`, `v6` (the first two end `child_claim_list_any_loop0`,
`child_claim_list_any_loop1`), the chain
buffer's size `g^(13 (a + b + 1))` at `v16`, the loops' start `1` at `v33`, `v51`. -/
def anyQ (n : ℕ) (σ : Val) : Prop :=
  σ (.n 4) = gen ^ (n / 136) ∧ σ (.n 5) = gen ^ (n % 136 / 17) ∧ σ (.n 6) = gen ^ (n % 17) ∧
    σ (.n 16) = gen ^ (13 * (n / 136 + n % 136 / 17 + 1)) ∧ σ (.n 33) = 1 ∧ σ (.n 51) = 1

/-- `child_claim_list_any`'s calls: `child_claim_list_any_loop0` when `n / 136 ≠ 0`,
`child_claim_list_any_loop1` when
`n % 136 / 17 ≠ 0`, `child_claim_list_last__L{n % 17}`. -/
def anyCalls (n : ℕ) (_ : Val) : List Call :=
  [⟨name% «child_claim_list_any_loop0», [.n 33, .n 4, .n 17, .n 0, .n 1, .n 2, .n 8], [],
      decide (n / 136 ≠ 0)⟩,
    ⟨name% «child_claim_list_any_loop1», [.n 51, .n 5, .n 39, .n 0, .n 1, .n 48, .n 8], [],
        decide (n % 136 / 17 ≠ 0)⟩,
    ⟨cclNames[n % 17]!, [.n 57, .n 0, .n 1, .n 63, .n 8], [.n 64, .n 65], true⟩]

/-- `child_claim_list_any`'s `HeapBuf`: the chain buffer. -/
def anyBufs (n : ℕ) (_ : Val) : List ℕ := [13 * (n / 136 + n % 136 / 17 + 1)]

/-- No constraint on `child_claim_list_any`'s callees. -/
def anyTs : List (Tree → Prop) := [fun _ => True, fun _ => True, fun _ => True]

/-- **`child_claim_list_any`'s honest shape** on `n` claims. -/
def anyHonest (n : ℕ) : Tree → Prop :=
  NodeHonest coreProgram "child_claim_list_any" (anyQ n) (anyCalls n) (anyBufs n) anyTs

/-- **`child_claim_list_any`'s words** on `n = 136a + 17b + c` claims: its frame, its chain buffer
`13 (a + b + 1)`, `child_claim_list_any_loop0` within `a + 1` frames (its frame when not entered),
`child_claim_list_any_loop1` within
`b + 1`, `child_claim_list_last__L{c}` a leaf within its frame. -/
def anyB (fs : String → ℕ) (n : ℕ) : ℕ :=
  fs "child_claim_list_any" + 13 * (n / 136 + n % 136 / 17 + 1) +
    ((if n / 136 ≠ 0 then (n / 136 + 1) * fs name% «child_claim_list_any_loop0» else fs
        name% «child_claim_list_any_loop0») +
      ((if n % 136 / 17 ≠ 0 then (n % 136 / 17 + 1) * fs name% «child_claim_list_any_loop1» else fs
          name% «child_claim_list_any_loop1») +
        (fs (cclNames.getD (n % 17) "") + 0)))

/-! ## Placed -/

set_option maxRecDepth 20000 in
/-- **`child_claim_list_any` is complete, placed, by a tree of honest shape, within its bound**:
`n < 136 · 2^20` honest records among the caller's words, its chain buffer after its frame
holding the states after each frame; it returns their cells' digest. -/
theorem child_claim_list_any_completeAtTB (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ}
    {Lin : Main.Layout} {eP rg L n : ℕ} {base : E} {o : ℕ → ℕ} {cells : List E}
    (hn : n < claimBig * bigFramesCap) (hl : cells.length = 4 * n)
    (hL33 : L < 2 ^ 33) (hLκ : L ≤ 2 ^ κ)
    (hrec : ∀ rd, MemL rd Lin → RecMem rd (gen ^ rg) (gen ^ L) (gen ^ eP) base n o cells)
    (hR2 : ∀ j < n, RegionL Lin (rg + o j))
    (hR3 : ∀ j < n, ∀ c < 4, RegionL Lin (eP + 4 * o j + c)) :
    CompleteAtDTB fs cert κ "child_claim_list_any" Lin
      [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ (n / 136), gen ^ (n % 136 / 17), gen ^ (n % 17)]
      (Returns (digestCells (keccak256 (cellsBytes cells)))) (anyHonest n) (anyB fs n) := by
  intro fp
  simp only [claimBig, bigFramesCap] at hn
  set a := n / 136 with hadef
  set b := n % 136 / 17 with hbdef
  set r := n % 17 with hrdef
  have hnm : n = 136 * a + 17 * b + r := by omega
  have ha20 : a < 1048576 := by omega
  have hb8 : b < 8 := by omega
  have hr17 : r < 17 := Nat.mod_lt _ (by norm_num)
  set b0 := fp + fs "child_claim_list_any" with hb0
  set chain : E := gen ^ b0 with hchain
  set Own : Main.Layout := [(b0, chainCells cells a b)] with hOwn
  set D := keccak256 (cellsBytes cells) with hD
  set last : E := gen ^ L * gen⁻¹ with hlastdef
  have hlast : last * gen = gen ^ L := by
    rw [hlastdef, mul_assoc, inv_mul_cancel₀ gen_ne_zero, mul_one]
  have hWo : Within Own b0 (13 * (a + b + 1)) := by
    intro q hq; simp only [hOwn, List.mem_singleton] at hq; subst hq
    simp [length_chainCells]
  have hDo : DisjL Own := List.pairwise_singleton _ _
  have hmOwn : ∀ rd, MemL rd Own → ReadsAt rd chain (chainCells cells a b) := fun rd hm =>
    reads_of_memL hm List.mem_cons_self
  have hOR : ∀ k < 13 * (a + b + 1), RegionL (Lin ++ Own) (b0 + k) := fun k hk =>
    regionL_append_right (regionL_of_mem (L := Own) List.mem_cons_self
      (by rw [length_chainCells]; exact hk))
  -- the callees
  let ks : List Kid :=
    [⟨name% «child_claim_list_any_loop0», decide (a ≠ 0), [1, gen ^ a, chain, gen ^ eP, gen ^ rg,
        base, last], Lin ++ Own,
        Returns []⟩,
      ⟨name% «child_claim_list_any_loop1», decide (b ≠ 0), [1, gen ^ b, chain * gen ^ (13 * a),
          gen ^ eP, gen ^ rg,
        base * gen ^ (136 * a), last], Lin ++ Own, Returns []⟩,
      ⟨cclNames[r]!, true, [chain * gen ^ (13 * (a + b)), gen ^ eP, gen ^ rg,
        base * gen ^ (136 * a + 17 * b), last], Lin ++ Own, Returns (digestCells D)⟩]
  have hokB : KidsDTB fs cert κ ks anyTs
      [(a + 1) * fs name% «child_claim_list_any_loop0», (b + 1) * fs
          name% «child_claim_list_any_loop1», fs (cclNames.getD r "")] := by
    refine ⟨fun ht => ?_, fun ht => ?_, fun _ => ?_, trivial⟩
    · simp only [decide_eq_true_eq] at ht
      refine anyLoop_completeAtB fs cert (j := 365)
        (find_of_idx any136_idx) any136_ok any136c_head
        any136c_edge any136c_recs any136_nb any136_unplaced (by norm_num)
        (chP := b0) (n0 := 0) (pre0 := []) (o := o) (cells := cells) rfl rfl rfl (by simp)
        (by rw [hl]; omega) hlast hL33 hLκ (by omega) (by omega)
        (fun rd hm => ⟨fun q hq => ?_, fun j hj => hrec rd (memL_append.mp hm).1 j (by omega)⟩)
        (fun q hq c hc => ?_) (fun i hi => regionL_append_left (hR2 i (by omega)))
        (fun i hi c hc => regionL_append_left (hR3 i (by omega) c hc))
      · have := state_of_reads (hmOwn rd (memL_append.mp hm).2) (t := q) (by omega)
        rw [clU_big hq] at this
        rw [List.nil_append, show 0 + 64 * q = 8 * (8 * q) by ring,
          show 4 * 136 * q = 68 * (8 * q) by ring]
        exact this
      · rw [Nat.add_assoc]; exact hOR _ (by omega)
    · simp only [decide_eq_true_eq] at ht
      refine anyLoop_completeAtB fs cert (j := 366)
        (find_of_idx any17_idx) any17_ok any17c_parts.1
        any17c_parts.2.1 any17c_parts.2.2 any17_nb any17_unplaced
        (by norm_num) (chP := b0 + 13 * a) (n0 := 64 * a)
        (pre0 := cellsBytes (cells.take (544 * a))) (o := fun i => o (136 * a + i))
        (cells := cells.drop (544 * a)) (by rw [hchain, ← pow_add]) rfl rfl
        (by
          rw [length_cellsBytes, List.length_take, Nat.min_eq_left (by omega)]
          show 16 * (544 * a) = 136 * (64 * a); ring)
        (by rw [List.length_drop, hl]; omega) hlast hL33 hLκ (by omega)
        (by omega)
        (fun rd hm => ⟨fun q hq => ?_, ?_⟩) (fun q hq c hc => ?_)
        (fun i hi => regionL_append_left (hR2 _ (by omega)))
        (fun i hi c hc => regionL_append_left (hR3 _ (by omega) c hc))
      · have := state_of_reads (hmOwn rd (memL_append.mp hm).2) (t := a + q) (by omega)
        rw [clU_grp] at this
        rw [mul_assoc, ← pow_add, ← Nat.mul_add, show 64 * a + 8 * q = 8 * (8 * a + q) by ring,
          ← cellsBytes_append, ← List.take_add, show 544 * a + 4 * 17 * q = 68 * (8 * a + q) by ring]
        exact this
      · have := recMem_drop (hrec rd (memL_append.mp hm).1) (s := 136 * a) (k := 17 * b) (by omega)
        rwa [show 4 * (136 * a) = 544 * a by ring] at this
      · rw [show b0 + 13 * a + 13 * q + c = b0 + (13 * a + 13 * q + c) by ring]
        exact hOR _ (by omega)
    · show CompleteAtDTB fs cert κ cclNames[r]! (Lin ++ Own) _ _ _ _
      rw [cclNames_get hr17]
      have hpre : (cellsBytes (cells.take (68 * (8 * a + b)))).length = rate * (8 * (8 * a + b)) := by
        rw [length_cellsBytes, List.length_take, Nat.min_eq_left (by omega)]
        show 16 * (68 * (8 * a + b)) = 136 * (8 * (8 * a + b)); ring
      have := ccl_completeAtB fs cert hr17 (Lin := Lin ++ Own) (sP := b0 + 13 * (a + b))
        (sp := chain * gen ^ (13 * (a + b)))
        (os := fun j => o (136 * a + 17 * b + j)) (cells := cells.drop (68 * (8 * a + b)))
        (n := 8 * (8 * a + b)) (pre := cellsBytes (cells.take (68 * (8 * a + b))))
        (marks := base * gen ^ (136 * a + 17 * b)) (by rw [hchain, ← pow_add]) rfl rfl hpre
        (by rw [List.length_drop, hl]; omega) hlast hL33 hLκ
        (fun rd hm => ⟨by
            have := state_of_reads (hmOwn rd (memL_append.mp hm).2) (le_refl (a + b))
            rwa [clU_last] at this, by
            have := recMem_drop (hrec rd (memL_append.mp hm).1) (s := 136 * a + 17 * b) (k := r)
              (by omega)
            rwa [show 4 * (136 * a + 17 * b) = 68 * (8 * a + b) by ring] at this⟩)
        (fun c hc => by rw [Nat.add_assoc]; exact hOR _ (by omega))
        (fun j hj => regionL_append_left (hR2 _ (by omega)))
        (fun j hj c hc => regionL_append_left (hR3 _ (by omega) c hc))
      rwa [← cellsBytes_append, List.take_append_drop] at this
  obtain ⟨Nk, Lk, outs, hNk, hoo, hW, hD, -, hKids⟩ :=
    kidsFromInT_of_kidsDTB (fs := fs) (cert := cert) κ ks anyTs
      [(a + 1) * fs name% «child_claim_list_any_loop0», (b + 1) * fs
          name% «child_claim_list_any_loop1», fs (cclNames.getD r "")] hokB
      (b0 + 13 * (a + b + 1))
  have hl0 : outs.length = 3 := hoo.length
  obtain ⟨o1, t1, rfl, hl1⟩ := exists_of_length_succ hl0
  obtain ⟨o2, t2, rfl, hl2⟩ := exists_of_length_succ hl1
  obtain ⟨o3, t3, rfl, hl3⟩ := exists_of_length_succ hl2
  obtain rfl := List.eq_nil_of_length_eq_zero hl3
  obtain ⟨h1, h2, h3, -⟩ := hoo
  refine ⟨fs "child_claim_list_any" + 13 * (a + b + 1) + Nk, Own ++ Lk, _, [], ?_, ⟨rfl, rfl⟩, ?_,
    by rw [List.nil_append]; exact disj_append hDo hD hWo hW le_rfl, fun rd hlow hm => ?_⟩
  · have hb := hNk
    simp only [kidsBoundL, ks, List.headD_cons, List.tail_cons, ↓reduceIte, decide_eq_true_eq] at hb
    simp only [anyB, ← hadef, ← hbdef, ← hrdef]
    exact Nat.add_le_add_left hb _
  · rw [List.nil_append, within_append]
    exact ⟨hWo.mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  simp only [List.nil_append] at hm
  obtain ⟨hm1, hLin'⟩ := memL_append.mp hm
  obtain ⟨hmO, hLk⟩ := memL_append.mp hm1
  have hch := hmOwn rd hmO
  have hz0 : StateAt rd chain 0 zeroState := by
    have := state_of_reads hch (Nat.zero_le (a + b))
    rw [Nat.mul_zero, pow_zero, mul_one, show clU a 0 = 0 by simp [clU]] at this
    exact this
  have hV := anyBody_core (rd := rd) (entries := gen ^ eP) (region := gen ^ rg) (base := base)
    (limit := gen ^ L) (a := a) (b := b) (c := r) D hz0
  set σ := anyσ rd [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ a, gen ^ b, gen ^ r] chain D with hσ
  have hpar := hV.par
  simp only [List.cons.injEq, and_true] at hpar
  obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := hpar
  have v8 : σ (.n 8) = last := by
    calc σ (.n 8) = σ (.n 8) * gen * gen⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ gen_ne_zero, mul_one]
      _ = last := by rw [hV.v8, e3]
  -- the path
  have hx : σ (.n 6) = ofK (addressOfIndex r) := by rw [e6, gen_pow_eq_ofK]
  have hw : walk σ (Fn.body fn% «child_claim_list_any») =
      .ret (anyP1.flatMap (Main.slEvs σ) ++ .call cclNames[r]! [.n 57, .n 0, .n 1, .n 63, .n 8]
        [.n 64, .n 65] :: anyPost.flatMap (Main.slEvs σ)) [.n 66, .n 67] := by
    rw [any_body]
    exact walk_dispatch σ anyP1 anyPost anyP1_straight anyPost_straight (.n 6) cclNames
      [.n 57, .n 0, .n 1, .n 63, .n 8] [.n 64, .n 65] [.n 66, .n 67] (i := r)
      (by simp [cclNames]; omega) (by simp [cclNames]) hx
  set es := anyP1.flatMap (Main.slEvs σ) ++ .call cclNames[r]! [.n 57, .n 0, .n 1, .n 63, .n 8]
    [.n 64, .n 65] :: anyPost.flatMap (Main.slEvs σ) with hes
  have hmE : ∀ s ∈ anyP1 ++ anyPost, ∀ x, s = .atom x → x.Holds rd σ := by
    intro s hs x rfl
    refine hV.atoms x (cl_mem_atoms ?_)
    rw [anyFlat_split]
    simp only [List.mem_append, List.mem_cons] at hs ⊢
    rcases hs with hs | hs <;> simp [hs]
  have hev : ∀ e ∈ es, e.Holds rd σ := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · refine slEvs_holds (fun s hs => ?_) e he
      have hk := List.all_eq_true.mp anyP1_kinds s hs
      simp only [Bool.or_eq_true] at hk
      rcases hk with (hk | hk) | hk
      · exact slOk_atomS hk (hmE s (by simp [hs]))
      · rw [stmtEqb_sound hk]
        show IsInK (σ (.n 32)); rw [hV.v32, ← pow_zero gen]; exact gen_pow_add_isInK _ _
      · rw [stmtEqb_sound hk]
        show IsInK (σ (.n 50)); rw [hV.v50, ← pow_zero gen]; exact gen_pow_add_isInK _ _
    rcases List.mem_cons.mp he with rfl | he
    · trivial
    · refine slEvs_holds (fun s hs => ?_) e he
      rw [anyPost_eq] at hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · show σ (.n 66) = σ (.n 64); rw [hV.v66, hV.v64]
      · show σ (.n 67) = σ (.n 65); rw [hV.v67, hV.v65]
  obtain ⟨hpd, hpa, hpad, hpc⟩ := Main.straight_parts σ _ anyP1_straight
  obtain ⟨hqd, hqa, hqad, hqc⟩ := Main.straight_parts σ _ anyPost_straight
  have hpostA : anyPost.filterMap Main.Stmt.allocSz = [] ∧ anyPost.filterMap Main.Stmt.addrS = [] ∧
      anyPost.filterMap Main.Stmt.callS = [] ∧ anyPost.filterMap B1.Stmt.loadS = [] := by
    rw [anyPost_eq]; exact ⟨rfl, rfl, rfl, rfl⟩
  have hal : allocs σ es = [13 * (a + b + 1)] := by
    rw [hes, es3_allocs, hpa, hqa, anyP1_allocs, hpostA.1]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, hV.v16, List.append_nil]
    rw [logG_gen_pow (show 13 * (a + b + 1) < 2 ^ 64 - 1 by omega)]
  have h32 : decide (σ (.n 32) ≠ 0) = decide (a ≠ 0) := by
    rw [hV.v32]; exact decide_eq_decide.mpr (one_add_gen_ne (by omega))
  have h50 : decide (σ (.n 50) ≠ 0) = decide (b ≠ 0) := by
    rw [hV.v50]; exact decide_eq_decide.mpr (one_add_gen_ne (by omega))
  have hcalls : calls es = [⟨name% «child_claim_list_any_loop0», [.n 33, .n 4, .n 17, .n 0, .n 1,
      .n 2, .n 8], [],
        decide (a ≠ 0)⟩,
      ⟨name% «child_claim_list_any_loop1», [.n 51, .n 5, .n 39, .n 0, .n 1, .n 48, .n 8], [],
          decide (b ≠ 0)⟩,
      ⟨cclNames[r]!, [.n 57, .n 0, .n 1, .n 63, .n 8], [.n 64, .n 65], true⟩] := by
    rw [hes, es3_calls, hpc, hqc, anyP1_calls, hpostA.2.2.1]
    simp only [List.map_cons, List.map_nil, Main.mkCall, h32, h50, List.cons_append,
      List.nil_append]
  have hown : ∀ i, b0 ≤ i → i < b0 + 13 * (a + b + 1) →
      ownData cert fp (fp + fs "child_claim_list_any") "child_claim_list_any"
        [13 * (a + b + 1)] es i :=
    fun i h1 h2 => Or.inl ⟨(13 * (a + b + 1), b0), List.Mem.head _, h1, h2⟩
  have h := relAtInWT_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    (R := RegionL Lin) (D := RegionL []) (fp := fp) (N := Nk)
    (args := [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ a, gen ^ b, gen ^ r]) (rets := digestCells D)
    (Dk := fun i => (fun _ => False) i ∨ outRegion ks [o1, o2, o3] i)
    coreProgram_wf find_child_claim_list_any (Or.inl any_loop)
    (by rw [any_param, e0, e1, e2, e3, e4, e5, e6]) hw
    (by show [σ (.n 66), σ (.n 67)] = _; rw [hV.v66, hV.v67]; rfl) hev
    (by
      rw [hal, hes, es3_allocDsts, hpd, hqd, anyP1_allocs, hpostA.1]
      simp only [List.map_cons, List.map_nil, List.append_nil, bases, hV.v17]
      rw [hchain, gen_pow_eq_ofK])
    (fun q hq => by
      rw [hes, es3_addrs, hpad, hqad, anyP1_addrs, hpostA.2.1] at hq
      simp at hq)
    anyTs ?_ ?_ (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
  · have h' := relAtInT_nodeHonest (Q := anyQ n) (cs := anyCalls n) (bs := anyBufs n) h
      find_child_claim_list_any hw ⟨e4, e5, e6, hV.v16, hV.v33, hV.v51⟩
      (by rw [hcalls]; rfl) (by rw [hal]; rfl) (by simp [anyCalls, anyTs])
    rw [hal] at h'
    simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at h'
    exact h'
  · rw [hcalls, hal]
    rw [List.sum_cons, List.sum_nil, Nat.add_zero]
    refine hKids rd σ _ _ _ ?_ hlow hLk ?_ (regionsOk_of fun k hk _ i hi => ?_)
    · refine ⟨rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl,
        fun _ => ⟨?_, ?_⟩, trivial⟩
      · show [σ (.n 33), σ (.n 4), σ (.n 17), σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 8)] = _
        rw [hV.v33, e4, hV.v17, e0, e1, e2, v8]
      · rename_i ht; rw [(h1 ht).1]; rfl
      · show [σ (.n 51), σ (.n 5), σ (.n 39), σ (.n 0), σ (.n 1), σ (.n 48), σ (.n 8)] = _
        rw [hV.v51, e5, hV.v39, e0, e1, hV.v48, e2, v8]
      · rename_i ht; rw [(h2 ht).1]; rfl
      · show [σ (.n 57), σ (.n 0), σ (.n 1), σ (.n 63), σ (.n 8)] = _
        rw [hV.v57, e0, e1, hV.v63, e2, v8]
      · rw [(h3 rfl).1]; show [σ (.n 64), σ (.n 65)] = _; rw [hV.v64, hV.v65]; rfl
    · intro q hq
      simp only [B1.Kid.lins, ks, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_append, or_assoc] at hq
      rcases hq with hq | hq | hq | hq | hq | hq <;> first | exact hLin' q hq | exact hmO q hq
    · simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl
      all_goals
        obtain ⟨q, hq, h1', h2'⟩ := hi
        rcases List.mem_append.mp hq with hq | hq
        · exact Or.inl (Or.inl ⟨q, hq, h1', h2'⟩)
        · simp only [hOwn, List.mem_singleton] at hq
          subst hq
          simp only [length_chainCells] at h2'
          exact Or.inl (Or.inr (hown i h1' h2'))
  · intro A hA
    rw [hes, es3_loads, B1.loadAddrs_straight σ _ anyP1_straight,
      B1.loadAddrs_straight σ _ anyPost_straight, anyP1_loads, hpostA.2.2.2] at hA
    simp only [List.map_nil, List.append_nil, List.map_map, List.mem_map, List.mem_range,
      Function.comp] at hA
    obtain ⟨c, hc13, rfl⟩ := hA
    refine ⟨b0 + c, by rw [hV.v17, hchain, limb0_gen_pow_mul], Or.inl ?_⟩
    rw [hal]
    exact hown _ (by omega) (by omega)

/-- **`child_claim_list_any` is complete, placed, by a tree of honest shape.** -/
theorem child_claim_list_any_completeAtT (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ}
    {Lin : Main.Layout} {eP rg L n : ℕ} {base : E} {o : ℕ → ℕ} {cells : List E}
    (hn : n < claimBig * bigFramesCap) (hl : cells.length = 4 * n)
    (hL33 : L < 2 ^ 33) (hLκ : L ≤ 2 ^ κ)
    (hrec : ∀ rd, MemL rd Lin → RecMem rd (gen ^ rg) (gen ^ L) (gen ^ eP) base n o cells)
    (hR2 : ∀ j < n, RegionL Lin (rg + o j))
    (hR3 : ∀ j < n, ∀ c < 4, RegionL Lin (eP + 4 * o j + c)) :
    CompleteAtDT fs cert κ "child_claim_list_any" Lin
      [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ (n / 136), gen ^ (n % 136 / 17), gen ^ (n % 17)]
      (Returns (digestCells (keccak256 (cellsBytes cells)))) (anyHonest n) :=
  (child_claim_list_any_completeAtTB fs cert hn hl hL33 hLκ hrec hR2 hR3).toDT

/-- **`child_claim_list_any` is complete, placed.** -/
theorem child_claim_list_any_completeAt (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ}
    {Lin : Main.Layout} {eP rg L n : ℕ} {base : E} {o : ℕ → ℕ} {cells : List E}
    (hn : n < claimBig * bigFramesCap) (hl : cells.length = 4 * n)
    (hL33 : L < 2 ^ 33) (hLκ : L ≤ 2 ^ κ)
    (hrec : ∀ rd, MemL rd Lin → RecMem rd (gen ^ rg) (gen ^ L) (gen ^ eP) base n o cells)
    (hR2 : ∀ j < n, RegionL Lin (rg + o j))
    (hR3 : ∀ j < n, ∀ c < 4, RegionL Lin (eP + 4 * o j + c)) :
    CompleteAtD fs cert κ "child_claim_list_any" Lin
      [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ (n / 136), gen ^ (n % 136 / 17), gen ^ (n % 17)]
      (Returns (digestCells (keccak256 (cellsBytes cells)))) :=
  (child_claim_list_any_completeAtT fs cert hn hl hL33 hLκ hrec hR2 hR3).toD

end
end LeanVM.Guest.B1.Digest
