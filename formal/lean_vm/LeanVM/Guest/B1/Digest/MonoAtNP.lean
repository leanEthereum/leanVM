/-
  LeanVM.Guest.B1.Digest.MonoAtNP

  `child_claim_list_mono` placed with its pops: its claims' gaps, in order (its body pops nothing of its own).
-/

module

public import LeanVM.Guest.B1.Digest.MonoAtP
public import LeanVM.Guest.Budget.BoundedR

/-!
# The gap walk, placed with its pops

* `gapTs rd pss`: the callees' trees popping `pss` on `rd`; `nodeHonest_true`, `nodeHonest_pops_noWit`: a node of
  honest shape so forgets them, and, with no witness hint of its own, pops them in order;
* `child_claim_list_mono_completeAtTBP`: `child_claim_list_mono_completeAtTB` popping its claims' gaps (`monoPss`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDT CompleteAtDTB CompleteAtDTBR KidsDTB KidsDTBR kidsFromInT_of_kidsDTB
  kidsFromInT_of_kidsDTBR kidsBoundL Returns Kid DisjL Within disj_append regionsOk_of within_append LowDef)
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append)
open LeanVM.Guest.B1.Da (SlOk slEvs_holds exists_of_length_succ limb0_gen_pow_mul reads_of_memL
  regionL_of_mem)
open LeanVM.Guest.Budget (NodeHonest)

@[expose] public section

/-- **The callees' trees popping `pss` on `rd`.** -/
def gapTs (rd : Reader) (pss : List (List Pop)) : List (Tree → Prop) :=
  pss.map fun p t => t.pops coreProgram rd = p

theorem kidsT_true : ∀ {cs : List Call} {Ts Ts' : List (Tree → Prop)} {ks : List Tree},
    KidsT cs Ts ks → Ts.length = Ts'.length → (∀ T ∈ Ts', ∀ t, T t) → KidsT cs Ts' ks
  | [], _, _, _, _, _, _ => trivial
  | _ :: _, _, [], _, _, _, _ => trivial
  | _ :: _, _, _ :: _, [], _, _, _ => trivial
  | _ :: _, [], _ :: _, _ :: _, _, hl, _ => by simp at hl
  | _ :: _, _ :: _, T' :: _, _ :: _, ⟨_, hs⟩, hl, hT =>
    ⟨fun _ => hT T' List.mem_cons_self _, kidsT_true hs (by simpa using hl)
      fun T hT' => hT T (List.mem_cons_of_mem _ hT')⟩

/-- **A node of honest shape forgets its callees' predicates** for ones that always hold. -/
theorem nodeHonest_true {f : String} {Q : Val → Prop} {cs : Val → List Call} {bs : Val → List ℕ}
    {Ts Ts' : List (Tree → Prop)} {t : Tree} (h : NodeHonest coreProgram f Q cs bs Ts t)
    (hl : Ts.length = Ts'.length) (hT : ∀ T ∈ Ts', ∀ t, T t) : NodeHonest coreProgram f Q cs bs Ts' t := by
  obtain ⟨σ, ks, rfl, hQ, hc, hlen, hK⟩ := h
  exact ⟨σ, ks, rfl, hQ, hc, hl ▸ hlen, kidsT_true hK hl hT⟩

/-- **A valid node of honest shape with no witness hint of its own** pops its callees' entries in call order. -/
theorem nodeHonest_pops_noWit {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    (hb : Stmt.noWitList fn.body = true) {Q : Val → Prop} {cs : Val → List Call} {bs : Val → List ℕ}
    {rd : Reader} {pss : List (List Pop)} {t : Tree} {args rets : List E}
    (hv : t.Valid coreProgram rd args rets) (hH : NodeHonest coreProgram f Q cs bs (gapTs rd pss) t)
    (hok : ∀ σ, Q σ → KidsPopsOk (cs σ) pss) : t.pops coreProgram rd = pss.flatten := by
  obtain ⟨σ, ks, rfl, hQ, hc, -, hK⟩ := hH
  rw [valid_pops_noWit hf hb hv]
  obtain ⟨fn', hf', -, es, vs, hw, -, -, hkv⟩ := hv
  rw [hf] at hf'
  cases hf'
  rw [hc fn es vs hf hw] at hkv
  rw [popsKids_of_kidsT hkv hK (hok σ hQ)]

theorem mono_noWit : Stmt.noWitList (Fn.body fn% «child_claim_list_mono») = true := by decide +kernel

/-- `child_claim_list_mono`'s callees' entries: the big frames' gaps, the groups', the last claims'. -/
noncomputable def monoPss (o : ℕ → ℕ) (a b r : ℕ) : List (List Pop) :=
  [gapPops o 0 (136 * a), gapPops o (136 * a) (17 * b), gapPops o (136 * a + 17 * b) r]

set_option maxRecDepth 20000 in
/-- **`child_claim_list_mono_completeAtTB` with its pops**: its tree pops its claims' gaps in order. -/
theorem child_claim_list_mono_completeAtTBP (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ}
    {Lin : Main.Layout} {eP rg L n : ℕ} {base : E} {o : ℕ → ℕ} {cells : List E}
    (hn : n < claimBig * bigFramesCap) (hl : cells.length = 4 * n) (hLκ : L < 2 ^ κ)
    (hinc : ∀ j < n, mStart o j ≤ o j) (hend : mStart o n ≤ L)
    (hrec : ∀ rd, MemL rd Lin → MRec rd (gen ^ rg) L (gen ^ eP) base n o cells)
    (hR2 : ∀ j < n, RegionL Lin (rg + o j))
    (hR3 : ∀ j < n, ∀ c < 4, RegionL Lin (eP + 4 * o j + c)) :
    CompleteAtDTBR fs cert κ "child_claim_list_mono" Lin
      [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ (n / 136), gen ^ (n % 136 / 17), gen ^ (n % 17)]
      (Returns (digestCells (keccak256 (cellsBytes cells))))
      (fun rd t => monoHonest n t ∧ t.pops coreProgram rd = gapPops o 0 n) (monoB fs n) := by
  intro fp
  simp only [claimBig, bigFramesCap] at hn
  set a := n / 136 with hadef
  set b := n % 136 / 17 with hbdef
  set r := n % 17 with hrdef
  have hnm : n = 136 * a + 17 * b + r := by omega
  have ha20 : a < 1048576 := by omega
  have hb8 : b < 8 := by omega
  have hr17 : r < 17 := Nat.mod_lt _ (by norm_num)
  set b0 := fp + fs "child_claim_list_mono" with hb0
  set chain : E := gen ^ b0 with hchain
  set Own : Main.Layout := [(b0, monoCells (gen ^ rg) (gen ^ eP) o cells a b)] with hOwn
  set D := keccak256 (cellsBytes cells) with hD
  have hWo : Within Own b0 (15 * (a + b + 1)) := by
    intro q hq; simp only [hOwn, List.mem_singleton] at hq; subst hq
    simp [length_monoCells]
  have hDo : DisjL Own := List.pairwise_singleton _ _
  have hmOwn : ∀ rd, MemL rd Own → ReadsAt rd chain (monoCells (gen ^ rg) (gen ^ eP) o cells a b) :=
    fun rd hm => reads_of_memL hm List.mem_cons_self
  have hOR : ∀ k < 15 * (a + b + 1), RegionL (Lin ++ Own) (b0 + k) := fun k hk =>
    regionL_append_right (regionL_of_mem (L := Own) List.mem_cons_self
      (by rw [length_monoCells]; exact hk))
  -- the callees
  let ks : List Kid :=
    [⟨name% «child_claim_list_mono_loop0», decide (a ≠ 0), [1, gen ^ a, chain, base], Lin ++ Own,
        Returns []⟩,
      ⟨name% «child_claim_list_mono_loop1», decide (b ≠ 0), [1, gen ^ b, chain * gen ^ (15 * a),
          base], Lin ++ Own, Returns []⟩,
      ⟨mlNames[r]!, true, [chain * gen ^ (15 * (a + b)), gen ^ rg, base, gen ^ L], Lin ++ Own,
        Returns (digestCells D)⟩]
  have hokB : KidsDTBR fs cert κ ks (fun rd => gapTs rd (monoPss o a b r))
      [(a + 1) * fs name% «child_claim_list_mono_loop0», (b + 1) * fs
          name% «child_claim_list_mono_loop1», fs (mlNames.getD r "")] := by
    refine ⟨fun ht => ?_, fun ht => ?_, fun _ => ?_, trivial⟩
    · simp only [decide_eq_true_eq] at ht
      refine monoLoop_completeAtBP (hwit := mono136_wits) fs cert mono136_find mono136_ok mc136_ok word_g136 word_g544
        mono136_nb mono136_unplaced (by norm_num) (by norm_num)
        (chP := b0) (eP := eP) (rg := rg) (entries := gen ^ eP) (region := gen ^ rg) (n0 := 0)
        (s0 := 0) (pre0 := []) (o := o) (cells := cells) (L := L) rfl rfl
        rfl (by simp) (by rw [hl]; omega) (by omega) (by omega) (by omega)
        (fun i hi => by rw [Nat.zero_add]; exact hinc i (by omega))
        (fun rd hm => ⟨fun q hq => ?_, fun j hj => ?_⟩)
        (fun q hq c hc => ?_) (fun i hi => ?_) (fun i hi c hc => ?_)
      · have := monoRec_of_reads (hmOwn rd (memL_append.mp hm).2) (t := q) (by omega)
        rw [clU_big hq] at this
        rw [List.nil_append, show 0 + 64 * q = 8 * (8 * q) by ring,
          show 4 * 136 * q = 68 * (8 * q) by ring, show 0 + 136 * q = 17 * (8 * q) by ring]
        exact this
      · simp only [Nat.zero_add]; exact hrec rd (memL_append.mp hm).1 j (by omega)
      · rw [Nat.add_assoc]; exact hOR _ (by omega)
      · rw [Nat.zero_add]; exact regionL_append_left (hR2 i (by omega))
      · rw [Nat.zero_add]; exact regionL_append_left (hR3 i (by omega) c hc)
    · simp only [decide_eq_true_eq] at ht
      refine monoLoop_completeAtBP (hwit := mono17_wits) fs cert mono17_find mono17_ok mc17_ok word_g17 word_g68
        mono17_nb mono17_unplaced (by norm_num) (by norm_num) (chP := b0 + 15 * a) (eP := eP) (rg := rg) (entries := gen ^ eP)
        (region := gen ^ rg) (n0 := 64 * a)
        (s0 := 136 * a) (pre0 := cellsBytes (cells.take (544 * a))) (o := o)
        (cells := cells.drop (544 * a)) (L := L) (by rw [hchain, ← pow_add]) rfl rfl
        (by
          rw [length_cellsBytes, List.length_take, Nat.min_eq_left (by omega)]
          show 16 * (544 * a) = 136 * (64 * a); ring)
        (by rw [List.length_drop, hl]; omega) (by omega) (by omega) (by omega)
        (fun i hi => hinc _ (by omega))
        (fun rd hm => ⟨fun q hq => ?_, ?_⟩) (fun q hq c hc => ?_)
        (fun i hi => regionL_append_left (hR2 _ (by omega)))
        (fun i hi c hc => regionL_append_left (hR3 _ (by omega) c hc))
      · have := monoRec_of_reads (hmOwn rd (memL_append.mp hm).2) (t := a + q) (by omega)
        rw [clU_grp] at this
        rw [mul_assoc, ← pow_add, ← Nat.mul_add, show 64 * a + 8 * q = 8 * (8 * a + q) by ring,
          ← cellsBytes_append, ← List.take_add, show 544 * a + 4 * 17 * q = 68 * (8 * a + q) by ring,
          show 136 * a + 17 * q = 17 * (8 * a + q) by ring]
        exact this
      · have := mRec_drop (hrec rd (memL_append.mp hm).1) (s := 136 * a) (k := 17 * b) (by omega)
        rwa [show 4 * (136 * a) = 544 * a by ring] at this
      · rw [show b0 + 15 * a + 15 * q + c = b0 + (15 * a + 15 * q + c) by ring]
        exact hOR _ (by omega)
    · show CompleteAtDTBR fs cert κ mlNames[r]! (Lin ++ Own) _ _ _ _
      rw [mlNames_get hr17]
      have hpre : (cellsBytes (cells.take (68 * (8 * a + b)))).length =
          rate * (8 * (8 * a + b)) := by
        rw [length_cellsBytes, List.length_take, Nat.min_eq_left (by omega)]
        show 16 * (68 * (8 * a + b)) = 136 * (8 * (8 * a + b)); ring
      have := mlc_completeAtBP fs cert hr17 (Lin := Lin ++ Own) (rP := b0 + 15 * (a + b))
        (rec := chain * gen ^ (15 * (a + b))) (s := 136 * a + 17 * b) (o := o) (eP := eP) (rg := rg)
        (entries := gen ^ eP) (region := gen ^ rg) (limit := gen ^ L)
        (cells := cells.drop (68 * (8 * a + b))) (n := 8 * (8 * a + b))
        (pre := cellsBytes (cells.take (68 * (8 * a + b)))) (mark := base) (L := L)
        (by rw [hchain, ← pow_add]) rfl rfl rfl hpre
        (by rw [List.length_drop, hl]; omega) (fun i hi => hinc _ (by omega))
        (by rw [show 136 * a + 17 * b + r = n by omega]; exact hend) hLκ
        (fun rd hm => ⟨by
            have := monoRec_of_reads (hmOwn rd (memL_append.mp hm).2) (le_refl (a + b))
            rwa [clU_last, show 17 * (8 * a + b) = 136 * a + 17 * b by ring] at this, by
            have := mRec_drop (hrec rd (memL_append.mp hm).1) (s := 136 * a + 17 * b) (k := r)
              (by omega)
            rwa [show 4 * (136 * a + 17 * b) = 68 * (8 * a + b) by ring] at this⟩)
        (fun c hc => by rw [Nat.add_assoc]; exact hOR _ (by omega))
        (fun j hj => regionL_append_left (hR2 _ (by omega)))
        (fun j hj c hc => regionL_append_left (hR3 _ (by omega) c hc))
      rwa [← cellsBytes_append, List.take_append_drop] at this
  obtain ⟨Nk, Lk, outs, hNk, hoo, hW, hD, -, hKids⟩ :=
    kidsFromInT_of_kidsDTBR (fs := fs) (cert := cert) κ ks (fun rd => gapTs rd (monoPss o a b r))
      [(a + 1) * fs name% «child_claim_list_mono_loop0», (b + 1) * fs
          name% «child_claim_list_mono_loop1», fs (mlNames.getD r "")] hokB
      (b0 + 15 * (a + b + 1))
  have hl0 : outs.length = 3 := hoo.length
  obtain ⟨o1, t1, rfl, hl1⟩ := exists_of_length_succ hl0
  obtain ⟨o2, t2, rfl, hl2⟩ := exists_of_length_succ hl1
  obtain ⟨o3, t3, rfl, hl3⟩ := exists_of_length_succ hl2
  obtain rfl := List.eq_nil_of_length_eq_zero hl3
  obtain ⟨h1, h2, h3, -⟩ := hoo
  refine ⟨fs "child_claim_list_mono" + 15 * (a + b + 1) + Nk, Own ++ Lk, _, [], ?_, ⟨rfl, rfl⟩,
    ?_, by rw [List.nil_append]; exact disj_append hDo hD hWo hW le_rfl, fun rd hlow hm => ?_⟩
  · have hb := hNk
    simp only [kidsBoundL, ks, List.headD_cons, List.tail_cons, ↓reduceIte, decide_eq_true_eq] at hb
    simp only [monoB, ← hadef, ← hbdef, ← hrdef]
    exact Nat.add_le_add_left hb _
  · rw [List.nil_append, within_append]
    exact ⟨hWo.mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  simp only [List.nil_append] at hm
  obtain ⟨hm1, hLin'⟩ := memL_append.mp hm
  obtain ⟨hmO, hLk⟩ := memL_append.mp hm1
  have hch := hmOwn rd hmO
  have hz0 : MonoRecAt rd chain 0 [] (gen ^ rg) (gen ^ eP) 0 := by
    have := monoRec_of_reads hch (Nat.zero_le (a + b))
    rw [Nat.mul_zero, pow_zero, mul_one, show clU a 0 = 0 by simp [clU]] at this
    simpa [mStart] using this
  have hV := monoBody_core (rd := rd) (entries := gen ^ eP) (region := gen ^ rg) (base := base)
    (limit := gen ^ L) (a := a) (b := b) (c := r) D hz0
  set σ := monoσ rd [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ a, gen ^ b, gen ^ r] chain D with hσ
  have hpar := hV.par
  simp only [List.cons.injEq, and_true] at hpar
  obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := hpar
  -- the path
  have hx : σ (.n 6) = ofK (addressOfIndex r) := by rw [e6, gen_pow_eq_ofK]
  have hw : walk σ (Fn.body fn% «child_claim_list_mono») =
      .ret (monoP1.flatMap (Main.slEvs σ) ++ .call mlNames[r]! [.n 49, .n 1, .n 2, .n 3]
        [.n 50, .n 51] :: monoPost.flatMap (Main.slEvs σ)) [.n 52, .n 53] := by
    rw [mono_body]
    exact walk_dispatch σ monoP1 monoPost monoP1_straight monoPost_straight (.n 6) mlNames
      [.n 49, .n 1, .n 2, .n 3] [.n 50, .n 51] [.n 52, .n 53] (i := r)
      (by simp [mlNames]; omega) (by simp [mlNames]) hx
  set es := monoP1.flatMap (Main.slEvs σ) ++ .call mlNames[r]! [.n 49, .n 1, .n 2, .n 3]
    [.n 50, .n 51] :: monoPost.flatMap (Main.slEvs σ) with hes
  have hmE : ∀ s ∈ monoP1 ++ monoPost, ∀ x, s = .atom x → x.Holds rd σ := by
    intro s hs x rfl
    refine hV.atoms x (cl_mem_atoms ?_)
    rw [monoFlat_split]
    simp only [List.mem_append, List.mem_cons] at hs ⊢
    rcases hs with hs | hs <;> simp [hs]
  have hev : ∀ e ∈ es, e.Holds rd σ := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · refine slEvs_holds (fun s hs => ?_) e he
      have hk := List.all_eq_true.mp monoP1_kinds s hs
      simp only [Bool.or_eq_true] at hk
      rcases hk with (hk | hk) | hk
      · exact slOk_atomS hk (hmE s (by simp [hs]))
      · rw [stmtEqb_sound hk]
        show IsInK (σ (.n 31)); rw [hV.v31, ← pow_zero gen]; exact gen_pow_add_isInK _ _
      · rw [stmtEqb_sound hk]
        show IsInK (σ (.n 41)); rw [hV.v41, ← pow_zero gen]; exact gen_pow_add_isInK _ _
    rcases List.mem_cons.mp he with rfl | he
    · trivial
    · refine slEvs_holds (fun s hs => ?_) e he
      rw [monoPost_eq] at hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · show σ (.n 52) = σ (.n 50); rw [hV.v52, hV.v50]
      · show σ (.n 53) = σ (.n 51); rw [hV.v53, hV.v51]
  obtain ⟨hpd, hpa, hpad, hpc⟩ := Main.straight_parts σ _ monoP1_straight
  obtain ⟨hqd, hqa, hqad, hqc⟩ := Main.straight_parts σ _ monoPost_straight
  have hpostA : monoPost.filterMap Main.Stmt.allocSz = [] ∧
      monoPost.filterMap Main.Stmt.addrS = [] ∧
      monoPost.filterMap Main.Stmt.callS = [] ∧ monoPost.filterMap B1.Stmt.loadS = [] := by
    rw [monoPost_eq]; exact ⟨rfl, rfl, rfl, rfl⟩
  have hal : allocs σ es = [15 * (a + b + 1)] := by
    rw [hes, es3_allocs, hpa, hqa, monoP1_allocs, hpostA.1]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, hV.v15, List.append_nil]
    rw [logG_gen_pow (show 15 * (a + b + 1) < 2 ^ 64 - 1 by omega)]
  have h31 : decide (σ (.n 31) ≠ 0) = decide (a ≠ 0) := by
    rw [hV.v31]; exact decide_eq_decide.mpr (one_add_gen_ne (by omega))
  have h41 : decide (σ (.n 41) ≠ 0) = decide (b ≠ 0) := by
    rw [hV.v41]; exact decide_eq_decide.mpr (one_add_gen_ne (by omega))
  have hcalls : calls es = [⟨name% «child_claim_list_mono_loop0», [.n 32, .n 4, .n 16, .n 2], [],
        decide (a ≠ 0)⟩,
      ⟨name% «child_claim_list_mono_loop1», [.n 42, .n 5, .n 39, .n 2], [], decide (b ≠ 0)⟩,
      ⟨mlNames[r]!, [.n 49, .n 1, .n 2, .n 3], [.n 50, .n 51], true⟩] := by
    rw [hes, es3_calls, hpc, hqc, monoP1_calls, hpostA.2.2.1]
    simp only [List.map_cons, List.map_nil, Main.mkCall, h31, h41, List.cons_append,
      List.nil_append]
  have hown : ∀ i, b0 ≤ i → i < b0 + 15 * (a + b + 1) →
      ownData cert fp (fp + fs "child_claim_list_mono") "child_claim_list_mono"
        [15 * (a + b + 1)] es i :=
    fun i h1 h2 => Or.inl ⟨(15 * (a + b + 1), b0), List.Mem.head _, h1, h2⟩
  have h := relAtInWT_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    (R := RegionL Lin) (D := RegionL []) (fp := fp) (N := Nk)
    (args := [gen ^ eP, gen ^ rg, base, gen ^ L, gen ^ a, gen ^ b, gen ^ r]) (rets := digestCells D)
    (Dk := fun i => (fun _ => False) i ∨ outRegion ks [o1, o2, o3] i)
    coreProgram_wf find_child_claim_list_mono (Or.inl mono_loop)
    (by rw [mono_param, e0, e1, e2, e3, e4, e5, e6]) hw
    (by show [σ (.n 52), σ (.n 53)] = _; rw [hV.v52, hV.v53]; rfl) hev
    (by
      rw [hal, hes, es3_allocDsts, hpd, hqd, monoP1_allocs, hpostA.1]
      simp only [List.map_cons, List.map_nil, List.append_nil, bases, hV.v16]
      rw [hchain, gen_pow_eq_ofK])
    (fun q hq => by
      rw [hes, es3_addrs, hpad, hqad, monoP1_addrs, hpostA.2.1] at hq
      simp at hq)
    (gapTs rd (monoPss o a b r)) ?_ ?_ (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
  · have h' := relAtInT_nodeHonest (Q := monoQ n) (cs := monoCalls n) (bs := monoBufs n) h
      find_child_claim_list_mono hw ⟨e4, e5, e6, hV.v15, hV.v32, hV.v42⟩
      (by rw [hcalls]; rfl) (by rw [hal]; rfl) (by simp [monoCalls, gapTs, monoPss])
    rw [hal] at h'
    simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at h'
    obtain ⟨t, ht, hH⟩ := h'
    refine ⟨t, ht, nodeHonest_true hH (by simp [gapTs, monoPss, monoTs]) (by simp [monoTs]), ?_⟩
    rw [nodeHonest_pops_noWit find_child_claim_list_mono mono_noWit ht.2.1 hH fun σ' _ => ?_]
    · simp only [monoPss, List.flatten_cons, List.flatten_nil, List.append_nil]
      have e1 := gapPops_append o 0 (136 * a) (17 * b)
      have e2 := gapPops_append o 0 (136 * a + 17 * b) r
      rw [Nat.zero_add] at e1 e2
      rw [← List.append_assoc, e1, e2, hnm]
    · refine ⟨fun h0 => ?_, fun h0 => ?_, fun h0 => absurd h0 (by simp), trivial⟩
      · simp only [decide_eq_false_iff_not, not_not] at h0
        rw [← hadef] at h0
        simp [gapPops, h0]
      · simp only [decide_eq_false_iff_not, not_not] at h0
        rw [← hbdef] at h0
        simp [gapPops, h0]
  · rw [hcalls, hal]
    rw [List.sum_cons, List.sum_nil, Nat.add_zero]
    refine hKids rd σ _ _ _ ?_ hlow hLk ?_ (regionsOk_of fun k hk _ i hi => ?_)
    · refine ⟨rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl,
        fun _ => ⟨?_, ?_⟩, trivial⟩
      · show [σ (.n 32), σ (.n 4), σ (.n 16), σ (.n 2)] = _
        rw [hV.v32, e4, hV.v16, e2]
      · rename_i ht; rw [(h1 ht).1]; rfl
      · show [σ (.n 42), σ (.n 5), σ (.n 39), σ (.n 2)] = _
        rw [hV.v42, e5, hV.v39, e2]
      · rename_i ht; rw [(h2 ht).1]; rfl
      · show [σ (.n 49), σ (.n 1), σ (.n 2), σ (.n 3)] = _
        rw [hV.v49, e1, e2, e3]
      · rw [(h3 rfl).1]; show [σ (.n 50), σ (.n 51)] = _; rw [hV.v50, hV.v51]; rfl
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
          simp only [length_monoCells] at h2'
          exact Or.inl (Or.inr (hown i h1' h2'))
  · intro A hA
    rw [hes, es3_loads, B1.loadAddrs_straight σ _ monoP1_straight,
      B1.loadAddrs_straight σ _ monoPost_straight, monoP1_loads, hpostA.2.2.2] at hA
    simp only [List.map_nil, List.append_nil, List.map_map, List.mem_map, List.mem_range,
      Function.comp] at hA
    obtain ⟨c, hc15, rfl⟩ := hA
    refine ⟨b0 + c, by rw [hV.v16, hchain, limb0_gen_pow_mul], Or.inl ?_⟩
    rw [hal]
    exact hown _ (by omega) (by omega)


end
end LeanVM.Guest.B1.Digest
