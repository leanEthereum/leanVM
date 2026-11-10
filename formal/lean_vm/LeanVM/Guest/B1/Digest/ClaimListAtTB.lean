/-
  LeanVM.Guest.B1.Digest.ClaimListAtTB

  `claim_list_digest` in the uniform placed form by trees of honest shape, within a bound of its
  words before the memory (`clB`).
-/

module

public import LeanVM.Guest.B1.Digest.ClaimListAt
public import LeanVM.Guest.B1.Digest.LoopAtB
public import LeanVM.Guest.Memory.LoopPre
public import LeanVM.Guest.B1.Main.IterK

/-!
# `claim_list_digest`, within bounds

`clB fs SB SK n`: `claim_list_digest`'s words on `n = 136a + 17b + c` claims: its frame; when
`n ≠ 0`, its chain buffer `13 (a + b + 1)`, `list_split`'s bound `SB "list_split"`, `__loop15`'s
`a · iterK fs SK "__loop15"` and `__loop16`'s `b · iterK fs SK "__loop16"` and each loop's frame,
its run's phantom or, when not entered, the untaken call's, `claim_list_last__L{c}`'s `SB`. The
static bounds `SB`, `SK` are hypotheses (`TotalLe`, `TotalLeOn` on `LoopPre`). `list_split_completeAtDTB`: `list_split` within its bound.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1 (CompleteAtD CompleteAtDT CompleteAtDTB KidsDTB kidsFromInT_of_kidsDTB kidsBoundL
  Returns Kid DisjL Within disj_append completeAt_of_rel_pureB completeAt_of_rel_pureBat
  completeAtDTB_of_relIn regionsOk_of within_append bufL bufL_within bufL_disj bufL_region LowDef)
open LeanVM.Guest.B1.Main (Layout MemL RegionL memL_append iterK)
open LeanVM.Guest.B1.Da (SlOk slEvs_holds exists_of_length_succ limb0_gen_pow_mul reads_of_memL
  regionL_of_mem relAtIn_atoms)
open LeanVM.Guest.Budget (NodeHonest)

@[expose] public section

/-- **`claim_list_digest`'s words** on `n` claims. -/
def clB (fs : String → ℕ) (SB SK : String → ℕ) (n : ℕ) : ℕ :=
  if n = 0 then fs "claim_list_digest" else
    fs "claim_list_digest" + 13 * (n / 136 + n % 136 / 17 + 1) + (SB "list_split" +
      ((if n / 136 ≠ 0 then n / 136 * iterK fs SK "__loop15" + fs "__loop15" else fs "__loop15") +
        ((if n % 136 / 17 ≠ 0 then n % 136 / 17 * iterK fs SK "__loop16" + fs "__loop16"
          else fs "__loop16") +
          (SB clNames[n % 17]! + 0))))

/-- `list_split` within its static bound. -/
theorem list_split_completeAtDTB (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} {a b c : ℕ}
    (hκ : 16 ≤ κ) (ha : a < maxKeys) (hb : b < bigGroups) (hc : c < claimGroup) {Bls : ℕ}
    (hT : TotalLe coreProgram fs "list_split" (fun _ => Bls)) :
    CompleteAtDTB fs cert κ "list_split" [] [gen ^ (claimBig * a + claimGroup * b + c)]
      (Returns [gen ^ a, gen ^ b, gen ^ c]) (fun _ => True) Bls :=
  completeAtDTB_of_relIn list_split_pure (List.mem_singleton_self _)
    (fun rd t rets' hn hv hb => hT rd t _ rets' hn hv hb) fun rd hl _ =>
    Lift.relIn_of_leaf find_list_split list_split_leafOk
      (fun σ es vs _ hw A hA => by
        have hall : (Out.ret es vs).All (Lift.EvLeafOk noLoad) := by
          have := Lift.walk_leafOk (σ := σ) Data.core22.body list_split_leafOk
          exact (show walk σ Data.core22.body = .ret es vs from hw) ▸ this
        rw [loads_none hall] at hA
        exact absurd hA List.not_mem_nil)
      (list_split_complete' rd (hl.mono hκ) _ _ ⟨a, ha, b, hb, c, hc, rfl, rfl⟩)

set_option maxRecDepth 20000 in
/-- **`claim_list_digest` is complete, placed, by a tree of honest shape**: `n < 136 · 2^16`
canonical claims' cells at `g^eP` among the caller's words, its chain buffer after its frame
holding the states after each frame; it returns their digest's cells. -/
theorem claim_list_digest_completeAtTB (fs : String → ℕ) (cert : String → V → ℕ) {Lin : Main.Layout}
    {eP n : ℕ} {cells : List E} (hn : n < claimBig * maxKeys) (hl : cells.length = 4 * n)
    (hLe : ∀ rd, MemL rd Lin → ReadsAt rd (gen ^ eP) cells)
    (hLr : ∀ k < cells.length, RegionL Lin (eP + k)) {SB SK : String → ℕ}
    (hLS : TotalLe coreProgram fs "list_split" (fun _ => SB "list_split"))
    (hL15 : TotalLeOn coreProgram fs "__loop15" LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK "__loop15" + fs "__loop15"))
    (hL16 : TotalLeOn coreProgram fs "__loop16" LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK "__loop16" + fs "__loop16"))
    (hCL : ∀ j < 17, TotalLe coreProgram fs clNames[j]! (fun _ => SB clNames[j]!)) :
    CompleteAtDTB fs cert 16 "claim_list_digest" Lin [gen ^ eP, gen ^ n]
      (Returns (digestCells (keccak256 (cellsBytes cells))))
      (NodeHonest coreProgram "claim_list_digest" (clQ n) (clCalls n) (clBufs n) clTs)
      (clB fs SB SK n) := by
  intro fp
  simp only [claimBig, maxKeys] at hn
  have mH : ∀ s ∈ clHead, isAtomS s = true := by decide
  have mTl : ∀ s ∈ clTail, isAtomS s = true := by decide
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · -- the empty list
    have hcl : cells = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst hcl
    refine ⟨fs "claim_list_digest", [], _, [], by simp [clB], ⟨rfl, rfl⟩, fun q hq => by simp at hq,
      B1.disj_nil,
      fun rd hlow hm => ?_⟩
    obtain ⟨hat, e0, e1, h30, h3, hret⟩ := clz_core (rd := rd) (gen ^ eP)
    set σ := clzσ rd (gen ^ eP) with hσ
    have hb : (if σ (.n 3) = 0 then walk σ cl23Zero else walk σ cl23Else) =
        .fall (cl23Zero.flatMap (Main.slEvs σ)) := by
      simp only [h30, ↓reduceIte]; exact walk_straight_fall σ _ cl23Zero_straight
    have hw := walk_ite σ clTail clTail_straight (.n 3) cl23Zero cl23Else [.n 76, .n 77] _ hb
      clHead clHead_straight
    rw [← cl_body] at hw
    set es := clHead.flatMap (Main.slEvs σ) ++ .inK (.n 3) ::
      (cl23Zero.flatMap (Main.slEvs σ) ++ clTail.flatMap (Main.slEvs σ)) with hes
    have hmZ : ∀ s ∈ clHead ++ cl23Zero ++ clTail, ∀ a, s = .atom a → a.Holds rd σ := by
      intro s hs a rfl
      refine hat a (cl_mem_atoms ?_)
      unfold clZEval
      simp only [List.mem_append] at hs ⊢
      rcases hs with (hs | hs) | hs
      · exact Or.inl (Or.inl (Or.inl hs))
      · exact Or.inl (Or.inl (Or.inr hs))
      · exact Or.inr hs
    have hev : ∀ e ∈ es, e.Holds rd σ := by
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact slEvs_holds (fun s hs => slOk_atomS (mH s hs) (hmZ s (by simp [hs]))) e he
      rcases List.mem_cons.mp he with rfl | he
      · show IsInK (σ (.n 3)); rw [h3]; exact gen_pow_add_isInK 0 0
      rcases List.mem_append.mp he with he | he
      · exact slEvs_holds (fun s hs => slOk_atomS (List.all_eq_true.mp cl23Zero_atoms s hs)
          (hmZ s (by simp [hs]))) e he
      · exact slEvs_holds (fun s hs => slOk_atomS (mTl s hs) (hmZ s (by simp [hs]))) e he
    obtain ⟨hhd, hha, hhad, hhc⟩ := Main.straight_parts σ _ clHead_straight
    obtain ⟨hzd, hza, hzad, hzc⟩ := Main.straight_parts σ _ cl23Zero_straight
    obtain ⟨htd, hta, htad, htc⟩ := Main.straight_parts σ _ clTail_straight
    obtain ⟨z1, z2, z3, z4⟩ := cl23Zero_parts
    have hal : allocs σ es = [] := by
      rw [hes, allocs_append, show allocs σ (.inK (.n 3) :: (cl23Zero.flatMap (Main.slEvs σ) ++
        clTail.flatMap (Main.slEvs σ))) = allocs σ (cl23Zero.flatMap (Main.slEvs σ) ++
        clTail.flatMap (Main.slEvs σ)) from rfl, allocs_append, hha, hza, hta, z1]
      rfl
    have h := relAtInWT_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
      (R := RegionL Lin) (D := RegionL []) (Dk := fun _ => False) (N := 0) (fp := fp)
      (args := [gen ^ eP, gen ^ 0]) (rets := digestCells (keccak256 (cellsBytes [])))
      coreProgram_wf find_claim_list_digest (Or.inl cl_loop) (by rw [cl_param, e0, e1]) hw hret hev
      (by
        rw [hal, hes, allocDsts_append, show allocDsts (.inK (.n 3) :: (cl23Zero.flatMap
          (Main.slEvs σ) ++ clTail.flatMap (Main.slEvs σ))) = allocDsts (cl23Zero.flatMap
          (Main.slEvs σ) ++ clTail.flatMap (Main.slEvs σ)) from rfl, allocDsts_append, hhd, hzd, htd, z1]
        rfl)
      (fun q hq => by
        rw [hes, addrs_append, show addrs (.inK (.n 3) :: (cl23Zero.flatMap (Main.slEvs σ) ++
          clTail.flatMap (Main.slEvs σ))) = addrs (cl23Zero.flatMap (Main.slEvs σ) ++
          clTail.flatMap (Main.slEvs σ)) from rfl, addrs_append, hhad, hzad, htad, z2] at hq
        simp [clHead, clTail, Main.Stmt.addrS] at hq)
      clTs
      (by
        rw [hes, calls_append, show calls (.inK (.n 3) :: (cl23Zero.flatMap (Main.slEvs σ) ++
          clTail.flatMap (Main.slEvs σ))) = calls (cl23Zero.flatMap (Main.slEvs σ) ++
          clTail.flatMap (Main.slEvs σ)) from rfl, calls_append, hhc, hzc, htc, z3]
        exact ⟨rfl, fun _ h => h⟩)
      (fun A hA => by
        rw [hes, loadAddrs_append, show loadAddrs σ (.inK (.n 3) :: (cl23Zero.flatMap
          (Main.slEvs σ) ++ clTail.flatMap (Main.slEvs σ))) = loadAddrs σ (cl23Zero.flatMap
          (Main.slEvs σ) ++ clTail.flatMap (Main.slEvs σ)) from rfl, loadAddrs_append,
          B1.loadAddrs_straight σ _ clHead_straight, B1.loadAddrs_straight σ _ cl23Zero_straight,
          B1.loadAddrs_straight σ _ clTail_straight, z4] at hA
        simp [clHead, clTail, B1.Stmt.loadS] at hA)
      (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
    have hce : calls es = [] := by
      rw [hes, calls_append, show calls (.inK (.n 3) :: (cl23Zero.flatMap (Main.slEvs σ) ++
        clTail.flatMap (Main.slEvs σ))) = calls (cl23Zero.flatMap (Main.slEvs σ) ++
        clTail.flatMap (Main.slEvs σ)) from rfl, calls_append, hhc, hzc, htc, z3]
      rfl
    have h' := relAtInT_nodeHonest (Q := clQ 0) (cs := clCalls 0) (bs := clBufs 0) h
      find_claim_list_digest hw ⟨e1, fun h0 => absurd rfl h0⟩ (by rw [hce]; rfl) (by rw [hal]; rfl)
      (by simp [clCalls, clTs])
    rw [hal] at h'
    simpa using h'
  · -- a nonempty list
    set a := n / 136 with hadef
    set b := n % 136 / 17 with hbdef
    set r := n % 17 with hrdef
    have hnm : n = 136 * a + 17 * b + r := by omega
    have ha16 : a < 65536 := by omega
    have hb8 : b < 8 := by omega
    have hr17 : r < 17 := Nat.mod_lt _ (by norm_num)
    set b0 := fp + fs "claim_list_digest" with hb0
    set chain : E := gen ^ b0 with hchain
    set Own : Main.Layout := [(b0, chainCells cells a b)] with hOwn
    set D := keccak256 (cellsBytes cells) with hD
    have hWo : Within Own b0 (13 * (a + b + 1)) := by
      intro q hq; simp only [hOwn, List.mem_singleton] at hq; subst hq
      simp [length_chainCells]
    have hDo : DisjL Own := List.pairwise_singleton _ _
    have hmOwn : ∀ rd, MemL rd Own → ReadsAt rd chain (chainCells cells a b) := fun rd hm =>
      reads_of_memL hm List.mem_cons_self
    -- the callees
    let ks : List Kid :=
      [⟨"list_split", true, [gen ^ n], [], Returns [gen ^ a, gen ^ b, gen ^ r]⟩,
        ⟨"__loop15", decide (a ≠ 0), [1, gen ^ a, chain, gen ^ eP], Lin ++ Own, Returns []⟩,
        ⟨"__loop16", decide (b ≠ 0), [1, gen ^ b, chain * gen ^ (13 * a), gen ^ eP * gen ^ (544 * a)],
          Lin ++ Own, Returns []⟩,
        ⟨clNames[r]!, true, [chain * gen ^ (13 * (a + b)), gen ^ eP * gen ^ (544 * a + 68 * b)],
          Lin ++ Own, Returns (digestCells D)⟩]
    set Bs : List ℕ := [SB "list_split", a * iterK fs SK "__loop15" + fs "__loop15",
      b * iterK fs SK "__loop16" + fs "__loop16", SB clNames[r]!] with hBs
    have hokB : KidsDTB fs cert 16 ks clTs Bs := by
      refine ⟨fun _ => ?_, fun ht => ?_, fun ht => ?_, fun _ => ?_, trivial⟩
      · have := list_split_completeAtDTB fs cert (a := a) (b := b) (c := r) le_rfl
          (by simp [maxKeys]; omega) (by simp [bigGroups]; omega) (by simp [claimGroup]; omega) hLS
        rwa [show claimBig * a + claimGroup * b + r = n by simp [claimBig, claimGroup]; omega] at this
      · simp only [decide_eq_true_eq] at ht
        refine (completeAt_of_rel_pureBat big_pure (List.mem_singleton_self _) (fun rd hm => ?_) 16
          (B := a * iterK fs SK "__loop15" + fs "__loop15") (fun rd t hn hv hb => ?_)).toDTB
        · have hr := hLe rd (memL_append.mp hm).1
          have hmem := claimChainMem_of_reads hl hr (hmOwn rd (memL_append.mp hm).2)
          exact (guard_complete (find_of_idx big_idx (by rw [coreProgram_length]; omega))
            (grpc_shapeF grpc_big) (cl_bigBlocks hl hr hc hmem)).2 ((one_add_gen_ne (by omega)).mpr ht)
        · have := hL15 rd t _ _ hn (loopPre_gen (m := a) (by omega) (by omega) _) hv hb
          simpa [logG_gen_pow (show a < 2 ^ 64 - 1 by omega)] using this
      · simp only [decide_eq_true_eq] at ht
        refine (completeAt_of_rel_pureBat grp_pure (List.mem_singleton_self _) (fun rd hm => ?_) 16
          (B := b * iterK fs SK "__loop16" + fs "__loop16") (fun rd t hn hv hb => ?_)).toDTB
        · have hr := hLe rd (memL_append.mp hm).1
          have hmem := claimChainMem_of_reads hl hr (hmOwn rd (memL_append.mp hm).2)
          exact (guard_complete (find_of_idx grp_idx (by rw [coreProgram_length]; omega))
            (grpc_shapeF grpc_ok) (cl_grpBlocks hl hr hc hmem)).2 ((one_add_gen_ne (by omega)).mpr ht)
        · have := hL16 rd t _ _ hn (loopPre_gen (m := b) (by omega) (by omega) _) hv hb
          simpa [logG_gen_pow (show b < 2 ^ 64 - 1 by omega)] using this
      · have hT := hCL r hr17
        show CompleteAtDTB fs cert 16 clNames[r]! (Lin ++ Own) _ _ _ (SB clNames[r]!)
        rw [clNames_get hr17] at hT ⊢
        refine (completeAt_of_rel_pureB (cl_pure hr17) (List.mem_singleton_self _) (fun rd hm => ?_) 16
          (B := fun _ => SB (clNames.getD r "")) hT).toDTB
        have hr := hLe rd (memL_append.mp hm).1
        have hS := state_of_reads (hmOwn rd (memL_append.mp hm).2) (le_refl (a + b))
        rw [clU_last] at hS
        have hpre : (cellsBytes (cells.take (68 * (8 * a + b)))).length = rate * (8 * (8 * a + b)) := by
          rw [length_cellsBytes, List.length_take, Nat.min_eq_left (by omega)]
          show 16 * (68 * (8 * a + b)) = 136 * (8 * (8 * a + b)); omega
        have := claimLast_complete hr17 hpre hS (cells := cells.drop (68 * (8 * a + b)))
          (by simp; omega) (readsAt_drop' hr _) (canon_drop hc _)
        rw [← cellsBytes_append, List.take_append_drop] at this
        rw [show 544 * a + 68 * b = 68 * (8 * a + b) by ring]
        exact this
    obtain ⟨Nk, Lk, outs, hNk, hoo, hW, hD, -, hKids⟩ :=
      kidsFromInT_of_kidsDTB (fs := fs) (cert := cert) 16 ks clTs Bs hokB (b0 + 13 * (a + b + 1))
    have hl0 : outs.length = 4 := hoo.length
    obtain ⟨o1, t1, rfl, hl1⟩ := exists_of_length_succ hl0
    obtain ⟨o2, t2, rfl, hl2⟩ := exists_of_length_succ hl1
    obtain ⟨o3, t3, rfl, hl3⟩ := exists_of_length_succ hl2
    obtain ⟨o4, t4, rfl, hl4⟩ := exists_of_length_succ hl3
    obtain rfl := List.eq_nil_of_length_eq_zero hl4
    obtain ⟨h1, h2, h3, h4, -⟩ := hoo
    refine ⟨fs "claim_list_digest" + 13 * (a + b + 1) + Nk, Own ++ Lk, _, [], ?_, ⟨rfl, rfl⟩, ?_,
      by rw [List.nil_append]; exact disj_append hDo hD hWo hW le_rfl, fun rd hlow hm => ?_⟩
    · have hb := hNk
      simp only [kidsBoundL, ks, hBs, List.headD_cons, List.tail_cons, ↓reduceIte,
        decide_eq_true_eq] at hb
      simp only [clB, show n ≠ 0 by omega, ↓reduceIte, ← hadef, ← hbdef, ← hrdef]
      split_ifs at hb ⊢ <;> omega
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
    have hV := cl_core (rd := rd) (entries := gen ^ eP) (n := n) D hz0
    set σ := clσ rd (gen ^ eP) n chain D with hσ
    -- the path
    have h3ne : σ (.n 3) ≠ 0 := by
      rw [hV.v3, Ne, e_add_eq_zero_iff, pow_zero, gen_pow_eq_one_iff (by omega)]; omega
    have hx : σ (.n 14) = ofK (addressOfIndex r) := by rw [hV.v25, gen_pow_eq_ofK]
    have hb : (if σ (.n 3) = 0 then walk σ cl23Zero else walk σ cl23Else) =
        .fall (clP1.flatMap (Main.slEvs σ) ++ .call clNames[r]! [.n 65, .n 73] [.n 74, .n 75] ::
          clPost.flatMap (Main.slEvs σ)) := by
      simp only [h3ne, ↓reduceIte]
      rw [cl23Else_split]
      exact walk_dispatch_fall σ clP1 clPost clP1_straight (by rw [clPost_eq]; rfl) (.n 14) clNames
        [.n 65, .n 73] [.n 74, .n 75] (i := r) (by simp [clNames]; omega) (by simp [clNames]) hx
    have hw := walk_ite σ clTail clTail_straight (.n 3) cl23Zero cl23Else [.n 76, .n 77] _ hb
      clHead clHead_straight
    rw [← cl_body] at hw
    set es := clHead.flatMap (Main.slEvs σ) ++ .inK (.n 3) ::
      ((clP1.flatMap (Main.slEvs σ) ++ .call clNames[r]! [.n 65, .n 73] [.n 74, .n 75] ::
        clPost.flatMap (Main.slEvs σ)) ++ clTail.flatMap (Main.slEvs σ)) with hes
    have hmE : ∀ s ∈ clHead ++ clP1 ++ clTail, ∀ a, s = .atom a → a.Holds rd σ := by
      intro s hs a rfl
      refine hV.atoms a (cl_mem_atoms ?_)
      unfold clEEval
      rw [clElsePre_eq]
      simp only [List.mem_append] at hs ⊢
      rcases hs with (hs | hs) | hs <;> simp [hs]
    have hev : ∀ e ∈ es, e.Holds rd σ := by
      intro e he
      rcases List.mem_append.mp he with he | he
      · exact slEvs_holds (fun s hs => slOk_atomS (mH s hs) (hmE s (by simp [hs]))) e he
      rcases List.mem_cons.mp he with rfl | he
      · show IsInK (σ (.n 3)); rw [hV.v3]; exact gen_pow_add_isInK n 0
      rcases List.mem_append.mp he with he | he
      · rcases List.mem_append.mp he with he | he
        · refine slEvs_holds (fun s hs => ?_) e he
          have hk := List.all_eq_true.mp clP1_kinds s hs
          simp only [Bool.or_eq_true] at hk
          rcases hk with ((hk | hk) | hk) | hk
          · exact slOk_atomS hk (hmE s (by simp [hs]))
          · rw [stmtEqb_sound hk]; trivial
          · rw [stmtEqb_sound hk]
            show IsInK (σ (.n 38)); rw [hV.v49, ← pow_zero gen]; exact gen_pow_add_isInK _ _
          · rw [stmtEqb_sound hk]
            show IsInK (σ (.n 58)); rw [hV.v69, ← pow_zero gen]; exact gen_pow_add_isInK _ _
        rcases List.mem_cons.mp he with rfl | he
        · trivial
        · refine slEvs_holds (fun s hs => ?_) e he
          rw [clPost_eq] at hs
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl
          · show σ (.n 10) = σ (.n 74); rw [hV.v10, hV.v85]
          · show σ (.n 11) = σ (.n 75); rw [hV.v11, hV.v86]
      · exact slEvs_holds (fun s hs => slOk_atomS (mTl s hs) (hmE s (by simp [hs]))) e he
    obtain ⟨hhd, hha, hhad, hhc⟩ := Main.straight_parts σ _ clHead_straight
    obtain ⟨hpd, hpa, hpad, hpc⟩ := Main.straight_parts σ _ clP1_straight
    obtain ⟨hqd, hqa, hqad, hqc⟩ := Main.straight_parts σ _ (show clPost.all Main.Stmt.straight = true by rw [clPost_eq]; rfl)
    obtain ⟨htd, hta, htad, htc⟩ := Main.straight_parts σ _ clTail_straight
    have hpostA : clPost.filterMap Main.Stmt.allocSz = [] ∧ clPost.filterMap Main.Stmt.addrS = [] ∧
        clPost.filterMap Main.Stmt.callS = [] ∧ clPost.filterMap B1.Stmt.loadS = [] := by
      rw [clPost_eq]; exact ⟨rfl, rfl, rfl, rfl⟩
    have hal : allocs σ es = [13 * (a + b + 1)] := by
      rw [hes, es5_allocs, hha, hpa, hqa, hta, clP1_allocs, hpostA.1]
      simp only [clHead, clTail, List.filterMap_cons, List.filterMap_nil, Main.Stmt.allocSz,
        List.map_cons, List.map_nil, Sum.elim_inr, hV.v33,
        logG_gen_pow (show 13 * (n / 136 + n % 136 / 17 + 1) < 2 ^ 64 - 1 by omega), List.nil_append,
        List.append_nil]
      rfl
    have h49 : decide (σ (.n 38) ≠ 0) = decide (a ≠ 0) := by
      rw [hV.v49]; exact decide_eq_decide.mpr (one_add_gen_ne (by omega))
    have h69 : decide (σ (.n 58) ≠ 0) = decide (b ≠ 0) := by
      rw [hV.v69]; exact decide_eq_decide.mpr (one_add_gen_ne (by omega))
    have hcalls : calls es = [⟨"list_split", [.n 1], [.n 12, .n 13, .n 14], true⟩,
        ⟨"__loop15", [.n 39, .n 12, .n 23, .n 0], [], decide (a ≠ 0)⟩,
        ⟨"__loop16", [.n 59, .n 13, .n 45, .n 56], [], decide (b ≠ 0)⟩,
        ⟨clNames[r]!, [.n 65, .n 73], [.n 74, .n 75], true⟩] := by
      rw [hes, es5_calls, hhc, hpc, hqc, htc, clP1_calls, hpostA.2.2.1]
      simp only [List.map_cons, List.map_nil, Main.mkCall, h49, h69, clHead, clTail,
        List.filterMap_cons, List.filterMap_nil, Main.Stmt.callS, List.nil_append, List.cons_append,
        List.append_nil]
    have hown : ∀ i, b0 ≤ i → i < b0 + 13 * (a + b + 1) →
        ownData cert fp (fp + fs "claim_list_digest") "claim_list_digest" [13 * (a + b + 1)] es i :=
      fun i h1 h2 => Or.inl ⟨(13 * (a + b + 1), b0), List.Mem.head _, h1, h2⟩
    have h := relAtInWT_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
      (R := RegionL Lin) (D := RegionL []) (fp := fp) (N := Nk)
      (args := [gen ^ eP, gen ^ n]) (rets := digestCells D)
      (Dk := fun i => (fun _ => False) i ∨ outRegion ks [o1, o2, o3, o4] i)
      coreProgram_wf find_claim_list_digest (Or.inl cl_loop) (by rw [cl_param, hV.v0, hV.v1]) hw
      (by show [σ (.n 76), σ (.n 77)] = _; rw [hV.v87, hV.v88]; rfl) hev
      (by
        rw [hal, hes, es5_allocDsts, hhd, hpd, hqd, htd, clP1_allocs, hpostA.1]
        simp only [List.map_cons, List.map_nil, clHead, clTail, List.filterMap_cons,
          List.filterMap_nil, Main.Stmt.allocSz, List.nil_append, List.append_nil, bases, hV.v34]
        rw [hchain, gen_pow_eq_ofK])
      (fun q hq => by
        rw [hes, es5_addrs, hhad, hpad, hqad, htad, clP1_addrs, hpostA.2.1] at hq
        simp [clHead, clTail, Main.Stmt.addrS] at hq)
      clTs ?_ ?_ (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
    · have h' := relAtInT_nodeHonest (Q := clQ n) (cs := clCalls n) (bs := clBufs n) h
        find_claim_list_digest hw ⟨hV.v1, fun _ => ⟨hV.v23, hV.v24, hV.v25, hV.v33, hV.v50, hV.v70⟩⟩
        (by rw [hcalls]; unfold clCalls; split <;> first | omega | rfl)
        (by rw [hal]; unfold clBufs; split <;> first | omega | rfl)
        (by unfold clCalls; split <;> simp [clTs])
      rw [hal] at h'
      simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at h'
      exact h'
    · rw [hcalls, hal]
      rw [List.sum_cons, List.sum_nil, Nat.add_zero]
      refine hKids rd σ _ _ _ ?_ hlow hLk ?_ (regionsOk_of fun k hk _ i hi => ?_)
      · refine ⟨rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl,
          fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩, trivial⟩
        · show [σ (.n 1)] = _; rw [hV.v1]
        · rw [(h1 rfl).1]; show [σ (.n 12), σ (.n 13), σ (.n 14)] = _; rw [hV.v23, hV.v24, hV.v25]
        · show [σ (.n 39), σ (.n 12), σ (.n 23), σ (.n 0)] = _
          rw [hV.v50, hV.v23, hV.v34, hV.v0]
        · rename_i ht; rw [(h2 ht).1]; rfl
        · show [σ (.n 59), σ (.n 13), σ (.n 45), σ (.n 56)] = _
          rw [hV.v70, hV.v24, hV.v56, hV.v67]
        · rename_i ht; rw [(h3 ht).1]; rfl
        · show [σ (.n 65), σ (.n 73)] = _; rw [hV.v76, hV.v84]
        · rw [(h4 rfl).1]; show [σ (.n 74), σ (.n 75)] = _; rw [hV.v85, hV.v86]; rfl
      · intro q hq
        simp only [B1.Kid.lins, ks, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.nil_append, List.mem_append, or_assoc] at hq
        rcases hq with hq | hq | hq | hq | hq | hq <;> first | exact hLin' q hq | exact hmO q hq
      · simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl
        · obtain ⟨q, hq, -⟩ := hi; simp at hq
        all_goals
          obtain ⟨q, hq, h1', h2'⟩ := hi
          rcases List.mem_append.mp hq with hq | hq
          · exact Or.inl (Or.inl ⟨q, hq, h1', h2'⟩)
          · simp only [hOwn, List.mem_singleton] at hq
            subst hq
            simp only [length_chainCells] at h2'
            exact Or.inl (Or.inr (hown i h1' h2'))
    · intro A hA
      rw [hes, es5_loads, B1.loadAddrs_straight σ _ clHead_straight,
        B1.loadAddrs_straight σ _ clP1_straight,
        B1.loadAddrs_straight σ _ (show clPost.all Main.Stmt.straight = true by rw [clPost_eq]; rfl),
        B1.loadAddrs_straight σ _ clTail_straight, clP1_loads, hpostA.2.2.2] at hA
      simp only [clHead, clTail, List.filterMap_cons, List.filterMap_nil, B1.Stmt.loadS,
        List.map_nil, List.nil_append, List.append_nil, List.map_map, List.mem_map,
        List.mem_range, Function.comp] at hA
      obtain ⟨c, hc13, rfl⟩ := hA
      refine ⟨b0 + c, by rw [hV.v34, hchain, limb0_gen_pow_mul], Or.inl ?_⟩
      rw [hal]
      exact hown _ (by omega) (by omega)

end
end LeanVM.Guest.B1.Digest
