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
public import LeanVM.Guest.Data.NameStrings
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«claim_list_digest»
import LeanVM.Guest.Data.ValNames.«claim_list_chain»

/-!
# `claim_list_digest`, within bounds

`chB fs SB SK n`: `claim_list_chain`'s words on `n = 136a + 17b + c` claims: its frame, its chain buffer
`13 (a + b + 1)`, `claim_list_chain_loop0`'s `a · iterK fs SK "claim_list_chain_loop0"` and
`claim_list_chain_loop1`'s `b · iterK fs SK "claim_list_chain_loop1"` and each loop's frame, its run's phantom or,
when not entered, the untaken call's, `claim_list_tail`'s `SB`. `clB fs SB SK n`: `claim_list_digest`'s, its frame
and, when `n ≠ 0`, `list_split`'s bound `SB "list_split"` and `chB`. The static bounds `SB`, `SK` are hypotheses
(`TotalLe`, `TotalLeOn` on `LoopPre`). `list_split_completeAtDTB`: `list_split` within its bound.
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

/-- **`claim_list_chain`'s words** on `n = 136a + 17b + c` claims, `n ≠ 0`: its frame, its chain buffer
`13 (a + b + 1)`, `claim_list_chain_loop0`'s `a · iterK fs SK "claim_list_chain_loop0"` and
`claim_list_chain_loop1`'s `b · iterK fs SK "claim_list_chain_loop1"` and each loop's frame, its run's phantom or,
when not entered, the untaken call's tail, `claim_list_tail`'s `SB`. -/
def chB (fs : String → ℕ) (SB SK : String → ℕ) (n : ℕ) : ℕ :=
  fs "claim_list_chain" + 13 * (n / 136 + n % 136 / 17 + 1) +
    ((if n / 136 ≠ 0 then n / 136 * iterK fs SK name% «claim_list_chain_loop0» + fs
        name% «claim_list_chain_loop0» else fs (tailKey name% «claim_list_chain_loop0»)) +
      ((if n % 136 / 17 ≠ 0 then n % 136 / 17 * iterK fs SK name% «claim_list_chain_loop1» + fs
          name% «claim_list_chain_loop1»
        else fs (tailKey name% «claim_list_chain_loop1»)) +
        (SB "claim_list_tail" + 0)))

/-- **`claim_list_digest`'s words** on `n` claims: its frame; when `n ≠ 0`, `list_split`'s bound and `claim_list_chain`'s
words. -/
def clB (fs : String → ℕ) (SB SK : String → ℕ) (n : ℕ) : ℕ :=
  if n = 0 then fs "claim_list_digest" else
    fs "claim_list_digest" + (SB "list_split" + (chB fs SB SK n + 0))

/-- `list_split` within its static bound. -/
theorem list_split_completeAtDTB (fs : String → ℕ) (cert : String → V → ℕ) {κ : ℕ} {a b c : ℕ}
    (hκ : 20 ≤ κ) (ha : a < bigFramesCap) (hb : b < bigGroups) (hc : c < claimGroup) {Bls : ℕ}
    (hT : TotalLe coreProgram fs "list_split" (fun _ => Bls)) :
    CompleteAtDTB fs cert κ "list_split" [] [gen ^ (claimBig * a + claimGroup * b + c)]
      (Returns [gen ^ a, gen ^ b, gen ^ c]) (fun _ => True) Bls :=
  completeAtDTB_of_relIn list_split_pure (List.mem_singleton_self _)
    (fun rd t rets' hn hv hb => hT rd t _ rets' hn hv hb) fun rd hl _ =>
    Lift.relIn_of_leaf find_list_split list_split_leafOk
      (fun σ es vs _ hw A hA => by
        have hall : (Out.ret es vs).All (Lift.EvLeafOk noLoad) := by
          have := Lift.walk_leafOk (σ := σ) (fn% «list_split»).body list_split_leafOk
          exact (show walk σ (fn% «list_split»).body = .ret es vs from hw) ▸ this
        rw [loads_none hall] at hA
        exact absurd hA List.not_mem_nil)
      (list_split_complete' rd (hl.mono hκ) _ _ ⟨a, ha, b, hb, c, hc, rfl, rfl⟩)

set_option maxRecDepth 20000 in
/-- **`claim_list_chain` is complete, placed, by a tree of honest shape, within `chB`**: `0 < n < 136 · 2^20`
claims' cells at `g^eP` among the caller's words, its chain buffer after its frame holding the states after each
frame; it returns their digest's cells. -/
theorem claim_list_chain_completeAtTB (fs : String → ℕ) (cert : String → V → ℕ) {Lin : Main.Layout}
    {eP n : ℕ} {cells : List E} (hn : n < 2 ^ 23) (hl : cells.length = 4 * n)
    (hLe : ∀ rd, MemL rd Lin → ReadsAt rd (gen ^ eP) cells) {SB SK : String → ℕ}
    (hL15 : TotalLeOn coreProgram fs name% «claim_list_chain_loop0» LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK name% «claim_list_chain_loop0» + fs
          name% «claim_list_chain_loop0»))
    (hL16 : TotalLeOn coreProgram fs name% «claim_list_chain_loop1» LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK name% «claim_list_chain_loop1» + fs
          name% «claim_list_chain_loop1»))
    (hCL : TotalLe coreProgram fs "claim_list_tail" (fun _ => SB "claim_list_tail")) :
    CompleteAtDTB fs cert 23 "claim_list_chain" Lin
      [gen ^ eP, gen ^ n, gen ^ (n / 136), gen ^ (n % 136 / 17), gen ^ (n % 17)]
      (Returns (digestCells (keccak256 (cellsBytes cells)))) (chHonest n) (chB fs SB SK n) := by
  intro fp
  set a := n / 136 with hadef
  set b := n % 136 / 17 with hbdef
  set r := n % 17 with hrdef
  have hnm : n = 136 * a + 17 * b + r := by omega
  have ha20 : a < 1048576 := by omega
  have hb8 : b < 8 := by omega
  have hr17 : r < 17 := Nat.mod_lt _ (by norm_num)
  set b0 := fp + fs "claim_list_chain" with hb0
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
    [⟨name% «claim_list_chain_loop0», decide (a ≠ 0), [1, gen ^ a, chain, gen ^ eP],
          Lin ++ Own, Returns []⟩,
      ⟨name% «claim_list_chain_loop1», decide (b ≠ 0), [1, gen ^ b, chain * gen ^ (13 * a),
          gen ^ eP * gen ^ (544 * a)],
        Lin ++ Own, Returns []⟩,
      ⟨"claim_list_tail", true, [chain * gen ^ (13 * (a + b)), gen ^ eP * gen ^ (544 * a + 68 * b),
          gen ^ r], Lin ++ Own, Returns (digestCells D)⟩]
  set Bs : List ℕ := [a * iterK fs SK name% «claim_list_chain_loop0» + fs name% «claim_list_chain_loop0»,
    b * iterK fs SK name% «claim_list_chain_loop1» + fs name% «claim_list_chain_loop1», SB "claim_list_tail"] with hBs
  have hokB : KidsDTB fs cert 20 ks chTs Bs := by
    refine ⟨fun ht => ?_, fun ht => ?_, fun _ => ?_, trivial⟩
    · simp only [decide_eq_true_eq] at ht
      refine (completeAt_of_rel_pureBat big_pure (List.mem_singleton_self _) (fun rd hm => ?_) 20
        (B := a * iterK fs SK name% «claim_list_chain_loop0» + fs
            name% «claim_list_chain_loop0») (fun rd t hn hv hb => ?_)).toDTB
      · have hr := hLe rd (memL_append.mp hm).1
        have hmem := claimChainMem_of_reads hl hr (hmOwn rd (memL_append.mp hm).2)
        exact (guard_complete (find_of_idx big_idx)
          (grpc_shapeF grpc_big) (cl_bigBlocks hl hr hmem)).2 ((one_add_gen_ne (by omega)).mpr ht)
      · have := hL15 rd t _ _ hn (loopPre_gen (m := a) (by omega) (by omega) _) hv hb
        simpa [logG_gen_pow (show a < 2 ^ 64 - 1 by omega)] using this
    · simp only [decide_eq_true_eq] at ht
      refine (completeAt_of_rel_pureBat grp_pure (List.mem_singleton_self _) (fun rd hm => ?_) 20
        (B := b * iterK fs SK name% «claim_list_chain_loop1» + fs
            name% «claim_list_chain_loop1») (fun rd t hn hv hb => ?_)).toDTB
      · have hr := hLe rd (memL_append.mp hm).1
        have hmem := claimChainMem_of_reads hl hr (hmOwn rd (memL_append.mp hm).2)
        exact (guard_complete (find_of_idx grp_idx)
          (grpc_shapeF grpc_ok) (cl_grpBlocks hl hr hmem)).2 ((one_add_gen_ne (by omega)).mpr ht)
      · have := hL16 rd t _ _ hn (loopPre_gen (m := b) (by omega) (by omega) _) hv hb
        simpa [logG_gen_pow (show b < 2 ^ 64 - 1 by omega)] using this
    · refine (completeAt_of_rel_pureB tail_pure List.mem_cons_self (fun rd hm => ?_) 20
        (B := fun _ => SB "claim_list_tail") hCL).toDTB
      have hr := hLe rd (memL_append.mp hm).1
      have hS := state_of_reads (hmOwn rd (memL_append.mp hm).2) (le_refl (a + b))
      rw [clU_last] at hS
      have hpre : (cellsBytes (cells.take (68 * (8 * a + b)))).length = rate * (8 * (8 * a + b)) := by
        rw [length_cellsBytes, List.length_take, Nat.min_eq_left (by omega)]
        show 16 * (68 * (8 * a + b)) = 136 * (8 * (8 * a + b)); omega
      have := claimLast_complete hr17 hpre hS (cells := cells.drop (68 * (8 * a + b)))
        (by simp; omega) (readsAt_drop' hr _)
      rw [← cellsBytes_append, List.take_append_drop] at this
      rw [show 544 * a + 68 * b = 68 * (8 * a + b) by ring]
      exact tail_rel_of hr17 this
  obtain ⟨Nk, Lk, outs, hNk, hoo, hW, hD, -, hKids⟩ :=
    kidsFromInT_of_kidsDTB (fs := fs) (cert := cert) 20 ks chTs Bs hokB (b0 + 13 * (a + b + 1))
  have hl0 : outs.length = 3 := hoo.length
  obtain ⟨o1, t1, rfl, hl1⟩ := exists_of_length_succ hl0
  obtain ⟨o2, t2, rfl, hl2⟩ := exists_of_length_succ hl1
  obtain ⟨o3, t3, rfl, hl3⟩ := exists_of_length_succ hl2
  obtain rfl := List.eq_nil_of_length_eq_zero hl3
  obtain ⟨h1, h2, h3, -⟩ := hoo
  refine ⟨fs "claim_list_chain" + 13 * (a + b + 1) + Nk, Own ++ Lk, _, [], ?_, ⟨rfl, rfl⟩, ?_,
    by rw [List.nil_append]; exact disj_append hDo hD hWo hW le_rfl, fun rd hlow hm => ?_⟩
  · have hb := hNk
    simp only [kidsBoundL, ks, hBs, List.headD_cons, List.tail_cons, ↓reduceIte,
      decide_eq_true_eq] at hb
    simp only [chB, ← hadef, ← hbdef]
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
  have hV := chain_core (rd := rd) (entries := gen ^ eP) (n := n) D hz0 hlow hn
  set σ := chσ rd (gen ^ eP) n chain D with hσ
  -- the path
  have hw : walk σ (Fn.body fn% «claim_list_chain») =
      .ret (chP1.flatMap (Main.slEvs σ) ++ .call "claim_list_tail" [.n (val% «claim_list_chain» "last"), .n (val% «claim_list_chain» "d0~9"), .n (val% «claim_list_chain» "rest")] [.n (val% «claim_list_chain» "d0"), .n (val% «claim_list_chain» "d1")] ::
        chPost.flatMap (Main.slEvs σ)) [.n (val% «claim_list_chain» "s13#0"), .n (val% «claim_list_chain» "s13#0[1]")] := by
    rw [chain_body, ← List.cons_append, ← List.append_assoc, Main.walk_straight σ _ _ (by
      rw [List.all_append, chP1_straight, List.all_cons, chPost_straight]; rfl), List.flatMap_append,
      List.flatMap_cons]
    rfl
  set es := chP1.flatMap (Main.slEvs σ) ++ .call "claim_list_tail" [.n (val% «claim_list_chain» "last"), .n (val% «claim_list_chain» "d0~9"), .n (val% «claim_list_chain» "rest")] [.n (val% «claim_list_chain» "d0"), .n (val% «claim_list_chain» "d1")] ::
      chPost.flatMap (Main.slEvs σ) with hes
  have hmE : ∀ s ∈ chP1 ++ chPost, ∀ a, s = .atom a → a.Holds rd σ := by
    intro s hs a rfl
    refine hV.atoms a (cl_mem_atoms ?_)
    rw [chainFlat_split]
    simp only [List.mem_append, List.mem_cons] at hs ⊢
    rcases hs with hs | hs <;> simp [hs]
  have hev : ∀ e ∈ es, e.Holds rd σ := by
    intro e he
    rcases List.mem_append.mp he with he | he
    · refine slEvs_holds (fun s hs => ?_) e he
      have hk := List.all_eq_true.mp chP1_kinds s hs
      simp only [Bool.or_eq_true] at hk
      rcases hk with (hk | hk) | hk
      · exact slOk_atomS hk (hmE s (by simp [hs]))
      · rw [stmtEqb_sound hk]
        show IsInK (σ (.n (val% «claim_list_chain» "s2#1"))); rw [hV.v49, ← pow_zero gen]; exact gen_pow_add_isInK _ _
      · rw [stmtEqb_sound hk]
        show IsInK (σ (.n (val% «claim_list_chain» "s5#1"))); rw [hV.v69, ← pow_zero gen]; exact gen_pow_add_isInK _ _
    rcases List.mem_cons.mp he with rfl | he
    · trivial
    · refine slEvs_holds (fun s hs => ?_) e he
      rw [chPost_eq] at hs
      rcases List.mem_append.mp hs with hs' | hs'
      · exact slOk_atomS (List.all_eq_true.mp chChk_atoms s hs') (hmE s (by rw [chPost_eq]; simp [hs']))
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs'
        rcases hs' with rfl | rfl <;> exact slOk_atomS rfl (hmE _ (by rw [chPost_eq]; simp))
  obtain ⟨hpd, hpa, hpad, hpc⟩ := Main.straight_parts σ _ chP1_straight
  obtain ⟨hqd, hqa, hqad, hqc⟩ := Main.straight_parts σ _ chPost_straight
  have hal : allocs σ es = [13 * (a + b + 1)] := by
    rw [hes, es3_allocs, hpa, hqa, chP1_allocs, chPost_parts.1]
    simp only [List.map_cons, List.map_nil, Sum.elim_inr, hV.v33, List.append_nil]
    rw [logG_gen_pow (show 13 * (n / 136 + n % 136 / 17 + 1) < 2 ^ 64 - 1 by omega)]
  have h49 : decide (σ (.n (val% «claim_list_chain» "s2#1")) ≠ 0) = decide (a ≠ 0) := by
    rw [hV.v49]; exact decide_eq_decide.mpr (one_add_gen_ne (by omega))
  have h69 : decide (σ (.n (val% «claim_list_chain» "s5#1")) ≠ 0) = decide (b ≠ 0) := by
    rw [hV.v69]; exact decide_eq_decide.mpr (one_add_gen_ne (by omega))
  have hcalls : calls es = [⟨name% «claim_list_chain_loop0», [.n (val% «claim_list_chain» "s2#2"), .n (val% «claim_list_chain» "bigs"), .n (val% «claim_list_chain» "chain"), .n (val% «claim_list_chain» "entries_ptr")], [], decide (a ≠ 0)⟩,
      ⟨name% «claim_list_chain_loop1», [.n (val% «claim_list_chain» "s5#2"), .n (val% «claim_list_chain» "groups"), .n (val% «claim_list_chain» "mid"), .n (val% «claim_list_chain» "mid_entries")], [], decide (b ≠ 0)⟩,
      ⟨"claim_list_tail", [.n (val% «claim_list_chain» "last"), .n (val% «claim_list_chain» "d0~9"), .n (val% «claim_list_chain» "rest")], [.n (val% «claim_list_chain» "d0"), .n (val% «claim_list_chain» "d1")], true⟩] := by
    rw [hes, es3_calls, hpc, hqc, chP1_calls, chPost_parts.2.2.1]
    simp only [List.map_cons, List.map_nil, Main.mkCall, h49, h69, List.cons_append,
      List.nil_append]
  have hown : ∀ i, b0 ≤ i → i < b0 + 13 * (a + b + 1) →
      ownData cert fp (fp + fs "claim_list_chain") "claim_list_chain" [13 * (a + b + 1)] es i :=
    fun i h1 h2 => Or.inl ⟨(13 * (a + b + 1), b0), List.Mem.head _, h1, h2⟩
  have h := relAtInWT_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    (R := RegionL Lin) (D := RegionL []) (fp := fp) (N := Nk)
    (args := [gen ^ eP, gen ^ n, gen ^ a, gen ^ b, gen ^ r]) (rets := digestCells D)
    (Dk := fun i => (fun _ => False) i ∨ outRegion ks [o1, o2, o3] i)
    coreProgram_wf find_claim_list_chain (Or.inl ch_loop)
    (by rw [ch_param, hV.v0, hV.v1, hV.v23, hV.v24, hV.v25]) hw
    (by show [σ (.n (val% «claim_list_chain» "s13#0")), σ (.n (val% «claim_list_chain» "s13#0[1]"))] = _; rw [hV.v87, hV.v88]; rfl) hev
    (by
      rw [hal, hes, es3_allocDsts, hpd, hqd, chP1_allocs, chPost_parts.1]
      simp only [List.map_cons, List.map_nil, List.append_nil, bases, hV.v34]
      rw [hchain, gen_pow_eq_ofK])
    (fun q hq => by
      rw [hes, es3_addrs, hpad, hqad, chP1_addrs, chPost_parts.2.1] at hq
      simp at hq)
    chTs ?_ ?_ (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
  · have h' := relAtInT_nodeHonest (Q := chQ n) (cs := chCalls n) (bs := chBufs n) h
      find_claim_list_chain hw ⟨hV.v23, hV.v24, hV.v25, hV.v33, hV.v50, hV.v70⟩
      (by rw [hcalls]; rfl) (by rw [hal]; rfl) (by simp [chCalls, chTs])
    rw [hal] at h'
    simp only [List.sum_cons, List.sum_nil, Nat.add_zero] at h'
    exact h'
  · rw [hcalls, hal]
    rw [List.sum_cons, List.sum_nil, Nat.add_zero]
    refine hKids rd σ _ _ _ ?_ (hlow.mono (by norm_num)) hLk ?_ (regionsOk_of fun k hk _ i hi => ?_)
    · refine ⟨rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl,
        fun _ => ⟨?_, ?_⟩, trivial⟩
      · show [σ (.n (val% «claim_list_chain» "s2#2")), σ (.n (val% «claim_list_chain» "bigs")), σ (.n (val% «claim_list_chain» "chain")), σ (.n (val% «claim_list_chain» "entries_ptr"))] = _
        rw [hV.v50, hV.v23, hV.v34, hV.v0]
      · rename_i ht; rw [(h1 ht).1]; rfl
      · show [σ (.n (val% «claim_list_chain» "s5#2")), σ (.n (val% «claim_list_chain» "groups")), σ (.n (val% «claim_list_chain» "mid")), σ (.n (val% «claim_list_chain» "mid_entries"))] = _
        rw [hV.v70, hV.v24, hV.v56, hV.v67]
      · rename_i ht; rw [(h2 ht).1]; rfl
      · show [σ (.n (val% «claim_list_chain» "last")), σ (.n (val% «claim_list_chain» "d0~9")), σ (.n (val% «claim_list_chain» "rest"))] = _; rw [hV.v76, hV.v84, hV.v25]
      · rw [(h3 rfl).1]; show [σ (.n (val% «claim_list_chain» "d0")), σ (.n (val% «claim_list_chain» "d1"))] = _; rw [hV.v85, hV.v86]; rfl
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
    rw [hes, es3_loads, B1.loadAddrs_straight σ _ chP1_straight,
      B1.loadAddrs_straight σ _ chPost_straight, chP1_loads, chPost_parts.2.2.2] at hA
    simp only [List.map_nil, List.append_nil, List.map_map, List.mem_map, List.mem_range,
      Function.comp] at hA
    obtain ⟨c, hc13, rfl⟩ := hA
    refine ⟨b0 + c, by rw [hV.v34, hchain, limb0_gen_pow_mul], Or.inl ?_⟩
    rw [hal]
    exact hown _ (by omega) (by omega)

set_option maxRecDepth 20000 in
/-- **`claim_list_digest` is complete, placed, by a tree of honest shape, within `clB`**: `n < 136 · 2^20` claims'
cells at `g^eP` among the caller's words; it returns their digest's cells. -/
theorem claim_list_digest_completeAtTB (fs : String → ℕ) (cert : String → V → ℕ) {Lin : Main.Layout}
    {eP n : ℕ} {cells : List E} (hn : n < 2 ^ 23) (hl : cells.length = 4 * n)
    (hLe : ∀ rd, MemL rd Lin → ReadsAt rd (gen ^ eP) cells) {SB SK : String → ℕ}
    (hLS : TotalLe coreProgram fs "list_split" (fun _ => SB "list_split"))
    (hL15 : TotalLeOn coreProgram fs name% «claim_list_chain_loop0» LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK name% «claim_list_chain_loop0» + fs
          name% «claim_list_chain_loop0»))
    (hL16 : TotalLeOn coreProgram fs name% «claim_list_chain_loop1» LoopPre
      (fun a => logG (a.getD 1 0) * iterK fs SK name% «claim_list_chain_loop1» + fs
          name% «claim_list_chain_loop1»))
    (hCL : TotalLe coreProgram fs "claim_list_tail" (fun _ => SB "claim_list_tail")) :
    CompleteAtDTB fs cert 23 "claim_list_digest" Lin [gen ^ eP, gen ^ n]
      (Returns (digestCells (keccak256 (cellsBytes cells))))
      (NodeHonest coreProgram "claim_list_digest" (clQ n) (clCalls n) (clBufs n) (clTs n))
      (clB fs SB SK n) := by
  intro fp
  have mH : ∀ s ∈ clHead, isAtomS s = true := by decide
  have mTl : ∀ s ∈ clTail, isAtomS s = true := by decide
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · -- the empty list
    have hcl : cells = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    subst hcl
    refine ⟨fs "claim_list_digest", [], _, [], by simp [clB], ⟨rfl, rfl⟩, fun q hq => by simp at hq, B1.disj_nil,
      fun rd hlow hm => ?_⟩
    obtain ⟨hat, e0, e1, h30, h3, hret⟩ := clz_core (rd := rd) (gen ^ eP) (hlow.mono (by norm_num))
    set σ := clzσ rd (gen ^ eP) with hσ
    have hb : (if σ (.n (val% «claim_list_digest» "s1#1")) = 0 then walk σ cl23Zero else walk σ cl23Else) =
        .fall (cl23Zero.flatMap (Main.slEvs σ)) := by
      simp only [h30, ↓reduceIte]; exact walk_straight_fall σ _ cl23Zero_straight
    have hw := walk_ite σ clTail clTail_straight (.n (val% «claim_list_digest» "s1#1")) cl23Zero cl23Else [.n (val% «claim_list_digest» "s3#0"), .n (val% «claim_list_digest» "s3#0[1]")] _ hb
      clHead clHead_straight
    rw [← cl_body] at hw
    set es := clHead.flatMap (Main.slEvs σ) ++ .inK (.n (val% «claim_list_digest» "s1#1")) ::
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
      · show IsInK (σ (.n (val% «claim_list_digest» "s1#1"))); rw [h3]; exact gen_pow_add_isInK 0 0
      rcases List.mem_append.mp he with he | he
      · exact slEvs_holds (fun s hs => slOk_atomS (List.all_eq_true.mp cl23Zero_atoms s hs)
          (hmZ s (by simp [hs]))) e he
      · exact slEvs_holds (fun s hs => slOk_atomS (mTl s hs) (hmZ s (by simp [hs]))) e he
    obtain ⟨hhd, hha, hhad, hhc⟩ := Main.straight_parts σ _ clHead_straight
    obtain ⟨hzd, hza, hzad, hzc⟩ := Main.straight_parts σ _ cl23Zero_straight
    obtain ⟨htd, hta, htad, htc⟩ := Main.straight_parts σ _ clTail_straight
    obtain ⟨z1, z2, z3, z4⟩ := cl23Zero_parts
    have hal : allocs σ es = [] := by
      rw [hes, allocs_append, show allocs σ (.inK (.n (val% «claim_list_digest» "s1#1")) :: (cl23Zero.flatMap (Main.slEvs σ) ++
        clTail.flatMap (Main.slEvs σ))) = allocs σ (cl23Zero.flatMap (Main.slEvs σ) ++
        clTail.flatMap (Main.slEvs σ)) from rfl, allocs_append, hha, hza, hta, z1]
      rfl
    have h := relAtInWT_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
      (R := RegionL Lin) (D := RegionL []) (Dk := fun _ => False) (N := 0) (fp := fp)
      (args := [gen ^ eP, gen ^ 0]) (rets := digestCells (keccak256 (cellsBytes [])))
      coreProgram_wf find_claim_list_digest (Or.inl cl_loop) (by rw [cl_param, e0, e1]) hw hret hev
      (by
        rw [hal, hes, allocDsts_append, show allocDsts (.inK (.n (val% «claim_list_digest» "s1#1")) :: (cl23Zero.flatMap
          (Main.slEvs σ) ++ clTail.flatMap (Main.slEvs σ))) = allocDsts (cl23Zero.flatMap
          (Main.slEvs σ) ++ clTail.flatMap (Main.slEvs σ)) from rfl, allocDsts_append, hhd, hzd, htd, z1]
        rfl)
      (fun q hq => by
        rw [hes, addrs_append, show addrs (.inK (.n (val% «claim_list_digest» "s1#1")) :: (cl23Zero.flatMap (Main.slEvs σ) ++
          clTail.flatMap (Main.slEvs σ))) = addrs (cl23Zero.flatMap (Main.slEvs σ) ++
          clTail.flatMap (Main.slEvs σ)) from rfl, addrs_append, hhad, hzad, htad, z2] at hq
        simp [clHead, clTail, Main.Stmt.addrS] at hq)
      (clTs 0)
      (by
        rw [hes, calls_append, show calls (.inK (.n (val% «claim_list_digest» "s1#1")) :: (cl23Zero.flatMap (Main.slEvs σ) ++
          clTail.flatMap (Main.slEvs σ))) = calls (cl23Zero.flatMap (Main.slEvs σ) ++
          clTail.flatMap (Main.slEvs σ)) from rfl, calls_append, hhc, hzc, htc, z3]
        exact ⟨rfl, fun _ h => h⟩)
      (fun A hA => by
        rw [hes, loadAddrs_append, show loadAddrs σ (.inK (.n (val% «claim_list_digest» "s1#1")) :: (cl23Zero.flatMap
          (Main.slEvs σ) ++ clTail.flatMap (Main.slEvs σ))) = loadAddrs σ (cl23Zero.flatMap
          (Main.slEvs σ) ++ clTail.flatMap (Main.slEvs σ)) from rfl, loadAddrs_append,
          B1.loadAddrs_straight σ _ clHead_straight, B1.loadAddrs_straight σ _ cl23Zero_straight,
          B1.loadAddrs_straight σ _ clTail_straight, z4] at hA
        simp [clHead, clTail, B1.Stmt.loadS] at hA)
      (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
    have hce : calls es = [] := by
      rw [hes, calls_append, show calls (.inK (.n (val% «claim_list_digest» "s1#1")) :: (cl23Zero.flatMap (Main.slEvs σ) ++
        clTail.flatMap (Main.slEvs σ))) = calls (cl23Zero.flatMap (Main.slEvs σ) ++
        clTail.flatMap (Main.slEvs σ)) from rfl, calls_append, hhc, hzc, htc, z3]
      rfl
    have h' := relAtInT_nodeHonest (Q := clQ 0) (cs := clCalls 0) (bs := clBufs 0) h
      find_claim_list_digest hw ⟨e1, fun h0 => absurd rfl h0⟩ (by rw [hce]; rfl) (by rw [hal]; rfl)
      (by simp [clCalls, clTs])
    rw [hal] at h'
    simpa using h'
  · -- a nonempty list
    set D := keccak256 (cellsBytes cells) with hD
    let ks : List Kid :=
      [⟨"list_split", true, [gen ^ n], [], Returns [gen ^ (n / 136), gen ^ (n % 136 / 17), gen ^ (n % 17)]⟩,
        ⟨"claim_list_chain", true, [gen ^ eP, gen ^ n, gen ^ (n / 136), gen ^ (n % 136 / 17), gen ^ (n % 17)],
          Lin, Returns (digestCells D)⟩]
    have hokB : KidsDTB fs cert 23 ks (clTs n) [SB "list_split", chB fs SB SK n] := by
      refine ⟨fun _ => ?_, fun _ => claim_list_chain_completeAtTB fs cert hn hl hLe hL15 hL16 hCL, trivial⟩
      have := list_split_completeAtDTB fs cert (κ := 23) (a := n / 136) (b := n % 136 / 17) (c := n % 17)
        (by norm_num) (by simp [bigFramesCap]; omega) (by simp [bigGroups]; omega) (by simp [claimGroup]; omega) hLS
      rwa [show claimBig * (n / 136) + claimGroup * (n % 136 / 17) + n % 17 = n by
        simp [claimBig, claimGroup]; omega] at this
    obtain ⟨Nk, Lk, outs, hNk, hoo, hW, hDj, -, hKids⟩ :=
      kidsFromInT_of_kidsDTB (fs := fs) (cert := cert) 23 ks (clTs n) _ hokB (fp + fs "claim_list_digest")
    have hl0 : outs.length = 2 := hoo.length
    obtain ⟨o1, t1, rfl, hl1⟩ := exists_of_length_succ hl0
    obtain ⟨o2, t2, rfl, hl2⟩ := exists_of_length_succ hl1
    obtain rfl := List.eq_nil_of_length_eq_zero hl2
    obtain ⟨h1, h2, -⟩ := hoo
    refine ⟨fs "claim_list_digest" + Nk, Lk, _, [], ?_, ⟨rfl, rfl⟩, ?_, by rw [List.nil_append]; exact hDj,
      fun rd hlow hm => ?_⟩
    · have hb := hNk
      simp only [kidsBoundL, ks, List.headD_cons, List.tail_cons, ↓reduceIte] at hb
      simp only [clB, show n ≠ 0 by omega, ↓reduceIte]
      omega
    · rw [List.nil_append]; exact hW.mono (by omega) (by omega)
    simp only [List.nil_append] at hm
    obtain ⟨hLk, hLin'⟩ := memL_append.mp hm
    set σ := clEσ rd eP n D with hσ
    have hgn : gen ^ n ≠ 1 := fun h => (Nat.pos_iff_ne_zero.mp hn0) ((gen_pow_eq_one_iff (by omega)).mp h)
    have h3ne : σ (.n (val% «claim_list_digest» "s1#1")) ≠ 0 := by
      show gen ^ n + word 1 0 ≠ 0
      rw [word_one, Ne, e_add_eq_zero_iff]; exact hgn
    have hb : (if σ (.n (val% «claim_list_digest» "s1#1")) = 0 then walk σ cl23Zero else walk σ cl23Else) =
        .fall (cl23Else.flatMap (Main.slEvs σ)) := by
      simp only [h3ne, ↓reduceIte]; exact walk_straight_fall σ _ cl23Else_straight
    have hw := walk_ite σ clTail clTail_straight (.n (val% «claim_list_digest» "s1#1")) cl23Zero cl23Else [.n (val% «claim_list_digest» "s3#0"), .n (val% «claim_list_digest» "s3#0[1]")] _ hb
      clHead clHead_straight
    rw [← cl_body] at hw
    set es := clHead.flatMap (Main.slEvs σ) ++ .inK (.n (val% «claim_list_digest» "s1#1")) ::
      (cl23Else.flatMap (Main.slEvs σ) ++ clTail.flatMap (Main.slEvs σ)) with hes
    have hev : ∀ e ∈ es, e.Holds rd σ := by
      intro e he
      simp only [hes, cl23Else_eq, clHead, clTail, clSplitS, clChainS, List.flatMap_cons, List.flatMap_nil,
        Main.slEvs, List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · show σ (.n (val% «claim_list_digest» "s1#0")) = word 1 0; rfl
      · show σ (.n (val% «claim_list_digest» "s1#1")) = σ (.n (val% «claim_list_digest» "n_g")) + σ (.n (val% «claim_list_digest» "s1#0")); rfl
      · show IsInK (gen ^ n + word 1 0)
        rw [word_one, ← pow_zero gen]; exact gen_pow_add_isInK _ _
      · trivial
      · trivial
      · show σ (.n (val% «claim_list_digest» "digest[0]")) = σ (.n (val% «claim_list_digest» "d0")); rfl
      · show σ (.n (val% «claim_list_digest» "digest[1]")) = σ (.n (val% «claim_list_digest» "d1")); rfl
      · obtain ⟨t, ht⟩ := Sig.load_gpow hlow hn
        rw [← gen_pow_eq_ofK] at ht
        show LoadHolds rd (gen ^ n) 0 (rdAt rd (gen ^ n) 0)
        exact load_of_rdAt rfl ht.1 (by rw [ht.2]; rfl)
      · show σ (.n (val% «claim_list_digest» "s3#0")) = σ (.n (val% «claim_list_digest» "digest[0]")); rfl
      · show σ (.n (val% «claim_list_digest» "s3#0[1]")) = σ (.n (val% «claim_list_digest» "digest[1]")); rfl
    have hal : allocs σ es = [] := by simp [hes, cl23Else_eq, clHead, clTail, clSplitS, clChainS, allocs, Main.slEvs, Ev.alloc?]
    have hcalls : calls es = clCalls n σ := by
      simp only [clCalls, Nat.pos_iff_ne_zero.mp hn0, ↓reduceIte]
      simp only [hes, cl23Else_eq, clHead, clTail, clSplitS, clChainS, List.flatMap_cons, List.flatMap_nil,
        Main.slEvs, List.cons_append, List.nil_append, List.append_nil]
      rfl
    have h := relAtInWT_of_walk (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
      (R := RegionL Lin) (D := RegionL []) (fp := fp) (N := Nk)
      (args := [gen ^ eP, gen ^ n]) (rets := digestCells D)
      (Dk := fun i => (fun _ => False) i ∨ outRegion ks [o1, o2] i)
      coreProgram_wf find_claim_list_digest (Or.inl cl_loop) rfl hw rfl hev
      (by
        rw [hal]
        simp only [hes, cl23Else_eq, clHead, clTail, clSplitS, clChainS, List.flatMap_cons, List.flatMap_nil,
          Main.slEvs, List.cons_append, List.nil_append, List.append_nil]
        rfl)
      (fun q hq => by simp [hes, cl23Else_eq, clHead, clTail, clSplitS, clChainS, addrs, Main.slEvs, Ev.addr?] at hq)
      (clTs n) ?_ ?_ (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
    · have h' := relAtInT_nodeHonest (Q := clQ n) (cs := clCalls n) (bs := clBufs n) h
        find_claim_list_digest hw ⟨rfl, fun _ => ⟨rfl, rfl, rfl⟩⟩ hcalls (by rw [hal]; rfl)
        (by simp [clCalls, clTs, Nat.pos_iff_ne_zero.mp hn0])
      rw [hal] at h'
      simpa using h'
    · rw [hcalls, hal]
      simp only [clCalls, Nat.pos_iff_ne_zero.mp hn0, ↓reduceIte, List.sum_nil, Nat.add_zero]
      refine hKids rd σ _ _ _ ?_ hlow hLk ?_ (regionsOk_of fun k hk _ i hi => ?_)
      · refine ⟨rfl, rfl, fun _ => ⟨rfl, ?_⟩, rfl, rfl, fun _ => ⟨rfl, ?_⟩, trivial⟩
        · rw [(h1 rfl).1]; rfl
        · rw [(h2 rfl).1]; rfl
      · intro q hq
        simp only [Kid.lins, ks, List.flatMap_cons, List.flatMap_nil, List.append_nil,
          List.nil_append] at hq
        exact hLin' q hq
      · simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hk
        rcases hk with rfl | rfl
        · obtain ⟨q, hq, -⟩ := hi; simp at hq
        · exact Or.inl (Or.inl hi)
    · intro A hA
      simp [hes, cl23Else_eq, clHead, clTail, clSplitS, clChainS, loadAddrs, Main.slEvs, Ev.loadAddr?] at hA

end
end LeanVM.Guest.B1.Digest
