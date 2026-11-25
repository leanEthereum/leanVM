/-
  LeanVM.Guest.B1.Digest.ClaimListPops

  The entries every valid tree of `claim_list_digest` of honest shape pops: `list_split`'s split, then the claims in order, each its four cells as the memory holds them.
-/

module

public import LeanVM.Guest.B1.Digest.ValidPops
public import LeanVM.Guest.B1.Digest.ClaimListAt
import LeanVM.Guest.ValRef
import LeanVM.Guest.Data.ValNames.«claim_list_digest»
import LeanVM.Guest.Data.ValNames.«claim_list_chain»
import LeanVM.Guest.Data.ValNames.«claim_list_chain_loop0»
import LeanVM.Guest.Data.ValNames.«claim_list_chain_loop1»
import LeanVM.Guest.Data.ValNames.«claim_list_last__L»
import LeanVM.Guest.Data.ValNames.«claim_list_tail»
import LeanVM.Guest.Data.ValNames.«list_split»
import LeanVM.Guest.StmtsAppend

/-!
# `claim_list_digest`'s pops

* `claimPop rd e k`: claim `k` of a table at `g^e`, its four cells read off the memory;
* `list_split_pops`: a valid `list_split` pops its returns (`signers_split`);
* `grp_pops`: a frame loop of `m` claims from the counter `g^i` to `g^M` pops claims `m i ..< m M` of its table;
* `clLast_pops`: `claim_list_last__L{k}` pops its `k` claims;
* `ch_valid_pops`: a valid tree of `claim_list_chain` on `n` claims of honest shape pops the `n` claims;
* `cl_valid_pops`: a valid tree of `claim_list_digest` on `n` claims of honest shape pops the split, then the `n` claims.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.Budget (NodeHonest)

@[expose] public section

variable {rd : Reader}

/-- **Claim `k` of a table at `g^e`**: its four cells as the memory holds them. -/
noncomputable def claimPop (rd : Reader) (e k : ℕ) : Pop :=
  ("claims", (List.range 4).map fun c => (rd (addressOfIndex (e + 4 * k + c))).getD 0)

theorem claimPop_shift (e s k : ℕ) : claimPop rd (e + 4 * s) k = claimPop rd e (s + k) := by
  unfold claimPop
  congr 2
  funext c
  congr 3
  ring

theorem map_claimPop_shift (e s a n : ℕ) :
    (List.range' a n).map (claimPop rd (e + 4 * s)) = (List.range' (s + a) n).map (claimPop rd e) := by
  rw [List.range'_eq_map_range, List.range'_eq_map_range, List.map_map, List.map_map]
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp_apply, claimPop_shift]
  congr 1
  omega

theorem range'_zero_append (m k : ℕ) : List.range' 0 m ++ List.range' m k = List.range' 0 (m + k) := by
  simpa using List.range'_append_1 (s := 0) (m := m) (n := k)

/-- A heap destination through `g^a` reads the words from `g^(a + off)`. -/
theorem words_heap (σ : Val) {p : V} {a : ℕ} (hp : σ p = gen ^ a) (off len : ℕ) :
    Dest.words rd σ (.heap p off len) = (List.range len).map fun c => (rd (addressOfIndex (a + (off + c)))).getD 0 := by
  simp only [Dest.words, hp, gen_pow_eq_ofK, Main.addr_ofK]

/-! ## `list_split` -/

/-- `list_split`'s atoms. -/
noncomputable def lsAtoms : List Atom := (((atomsRet (fn% «list_split»).body).map Prod.fst).getD [])

theorem atomsRet_of {body : List Stmt} {vs : List V} (h : (atomsRet body).map Prod.snd = some vs) :
    atomsRet body = some (((atomsRet body).map Prod.fst).getD [], vs) := by
  cases e : atomsRet body with
  | none => rw [e] at h; exact absurd h (by simp)
  | some p => rw [e] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h; rfl

theorem ls_ok : (atomsRet (fn% «list_split»).body).map Prod.snd = some [.n (val% «list_split» "s9#0"), .n (val% «list_split» "s9#0[1]"), .n (val% «list_split» "s9#0[2]")] ∧
    lsAtoms.flatMap atomWit = [("signers_split", .stack [.n (val% «list_split» "split[0]"), .n (val% «list_split» "split[1]"), .n (val% «list_split» "split[2]")])] ∧
    lsAtoms.any (isCopyAt (.n (val% «list_split» "s9#0")) (.n (val% «list_split» "split[0]"))) = true ∧ lsAtoms.any (isCopyAt (.n (val% «list_split» "s9#0[1]")) (.n (val% «list_split» "split[1]"))) = true ∧
    lsAtoms.any (isCopyAt (.n (val% «list_split» "s9#0[2]")) (.n (val% «list_split» "split[2]"))) = true := by
  decide +kernel

/-- **A valid `list_split` pops its returns.** -/
theorem list_split_pops {t : Tree} {args rets : List E} (hn : t.name = "list_split")
    (hv : t.Valid coreProgram rd args rets) : t.pops coreProgram rd = [("signers_split", rets)] := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := ls_ok
  obtain ⟨σ, -, hr, hat, hp⟩ := valid_pops_atomsRet find_list_split (atomsRet_of h0) hn hv
  rw [hp, flatMap_atom_pops, ← lsAtoms, h1, ← hr]
  simp only [List.map_cons, List.map_nil, Dest.words, copy_sound h2 hat, copy_sound h3 hat, copy_sound h4 hat]

/-! ## The frame loops -/

/-- **A frame loop of `m` claims** (`grpOk`, its witness hints the claims at `.n ep`) from the counter `g^i` to `g^M`
pops claims `m i ..< m M` of the table at `g^e`. -/
theorem grp_pops {f : String} {j m c0 st0 ep : ℕ} (hidx : coreProgram.indexOf? f = some j)
    (hok : grpOk (coreProgram.getD j default) f m c0 st0 ep = true)
    (hw : (loopAtoms (coreProgram.getD j default)).flatMap atomWit =
      (List.range m).map fun k => ("claims", Dest.heap (.n ep) (4 * k) 4)) {M e : ℕ} (hM : M < 2 ^ 34) {chain : E} :
    ∀ d i (t : Tree) (rets : List E), i + 1 + d = M → t.name = f →
      t.Valid coreProgram rd [gen ^ i, gen ^ M, chain, gen ^ e] rets →
      t.pops coreProgram rd = (List.range' (m * i) (m * (M - i))).map (claimPop rd e) := by
  have hf := find_of_idx hidx
  simp only [grpOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hshape, hlen4⟩, -⟩, -⟩, -⟩, -⟩, -⟩, hmE⟩ := hok
  have hpar : (coreProgram.getD j default).params = [V.n 0, V.n 1, V.n 2, V.n 3] := by
    simp only [loopShape, Bool.and_eq_true, decide_eq_true_eq] at hshape
    rw [hshape.1.2, hlen4]; rfl
  -- one iteration's own claims
  have hown : ∀ i (σ : Val), σ (V.n 0) = gen ^ i → σ (V.n 3) = gen ^ e →
      (∀ a ∈ loopAtoms (coreProgram.getD j default), a.Holds rd σ) →
      (loopAtoms (coreProgram.getD j default)).flatMap (Atom.pops rd σ) =
        (List.range' (m * i) m).map (claimPop rd e) := by
    intro i σ h0 h3 hat
    have hE : σ (V.n ep) = gen ^ (e + 4 * m * i) := by
      rw [monoIs_sound hmE hat, h3, h0, ← pow_mul, ← pow_add]
      congr 1
      ring
    rw [flatMap_atom_pops, hw, List.map_map, List.range'_eq_map_range, List.map_map]
    refine List.map_congr_left fun k _ => ?_
    simp only [Function.comp_apply, words_heap σ hE, claimPop]
    congr 2
    funext c
    congr 3
    ring
  intro d
  induction d with
  | zero =>
    intro i t rets hi hn hv
    obtain ⟨σ, h0, hps, hat, h⟩ := valid_pops_loop hf hshape hn hv
    rw [hpar] at hps
    simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
    rcases h with ⟨-, hp⟩ | ⟨hne, -⟩
    · rw [hp, hown i σ h0 hps.2.2 hat, show M - i = 1 by omega, Nat.mul_one]
    · exact absurd (e_add_eq_zero_iff.mpr (by rw [← pow_succ, show i + 1 = M by omega]; rfl)) hne
  | succ d ih =>
    intro i t rets hi hn hv
    obtain ⟨σ, h0, hps, hat, h⟩ := valid_pops_loop hf hshape hn hv
    rw [hpar] at hps
    simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
    rcases h with ⟨h0', -⟩ | ⟨-, t', hn', hv', hp⟩
    · have := gen_pow_inj' (a := i + 1) (b := M) (by omega) hM
        (by rw [pow_succ]; exact e_add_eq_zero_iff.mp h0')
      omega
    · rw [← pow_succ] at hv'
      rw [hp, hown i σ h0 hps.2.2 hat, ih (i + 1) t' [] (by omega) hn' hv', ← List.map_append,
        show m * (i + 1) = m * i + m by ring, List.range'_append_1,
        show m * (M - i) = m + m * (M - (i + 1)) by
          rw [show M - i = M - (i + 1) + 1 by omega]; ring]

theorem big_wits : (loopAtoms (coreProgram.getD idx% «claim_list_chain_loop0» default)).flatMap atomWit =
    (List.range 136).map fun k => ("claims", Dest.heap (.n (val% «claim_list_chain_loop0» "blk")) (4 * k) 4) := by
  decide +kernel

theorem grp_wits : (loopAtoms (coreProgram.getD idx% «claim_list_chain_loop1» default)).flatMap atomWit =
    (List.range 17).map fun k => ("claims", Dest.heap (.n (val% «claim_list_chain_loop1» "blk")) (4 * k) 4) := by
  decide +kernel

/-- **A frame loop entered at `1`** (`callIf (1 + g^M) f [1, g^M, chain, g^e]`), or skipped when `M = 0`: claims
`0 ..< m M`. -/
theorem grp_pops_entry {f : String} {j m c0 st0 ep : ℕ} (hidx : coreProgram.indexOf? f = some j)
    (hok : grpOk (coreProgram.getD j default) f m c0 st0 ep = true)
    (hw : (loopAtoms (coreProgram.getD j default)).flatMap atomWit =
      (List.range m).map fun k => ("claims", Dest.heap (.n ep) (4 * k) 4)) {M e : ℕ} (hM : M < 2 ^ 34) {chain : E}
    {t : Tree} (hn : t.name = f) (hv : M ≠ 0 → t.Valid coreProgram rd [1, gen ^ M, chain, gen ^ e] [])
    (hph : M = 0 → ∃ g σ', t = .phantom g σ') :
    t.pops coreProgram rd = (List.range' 0 (m * M)).map (claimPop rd e) := by
  by_cases h0 : M = 0
  · obtain ⟨g, σ', rfl⟩ := hph h0
    rw [h0, Nat.mul_zero, Tree.pops]
    rfl
  · have h := hv h0
    rw [← pow_zero gen] at h
    rw [grp_pops hidx hok hw hM (M - 1) 0 t [] (by omega) hn h, Nat.mul_zero, Nat.sub_zero]

/-! ## The last claims -/

/-- `claim_list_last__L{k}`'s parameters, and its witness hints: the `k` claims at its second. -/
def clLastWitOk (k : ℕ) (fn : Fn) : Bool :=
  decide (fn.params = [V.n (valf% «claim_list_last» "state"), V.n (valf% «claim_list_last» "blk")]) &&
    decide (((atomsRet fn.body).map fun p => p.1.flatMap atomWit) =
      some ((List.range k).map fun j => ("claims", Dest.heap (.n (valf% «claim_list_last» "blk")) (4 * j) 4)))

theorem clLast_wit_all : ∀ k < 17, clLastWitOk k (coreProgram.getD (idx% «claim_list_last__L0» + k) default) = true := by
  decide +kernel

/-- **`claim_list_last__L{k}`** called on `[sp, g^e]` pops claims `0 ..< k` of the table at `g^e`. -/
theorem clLast_pops {k : ℕ} (hk : k < 17) {t : Tree} {sp : E} {e : ℕ} {rets : List E}
    (hn : t.name = clNames.getD k "") (hv : t.Valid coreProgram rd [sp, gen ^ e] rets) :
    t.pops coreProgram rd = (List.range' 0 k).map (claimPop rd e) := by
  have hf := find_of_idx (cl_idx k hk)
  have hok := clLast_wit_all k hk
  simp only [clLastWitOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hpar, hw⟩ := hok
  cases e' : atomsRet (coreProgram.getD (idx% «claim_list_last__L0» + k) default).body with
  | none => rw [e'] at hw; exact absurd hw (by simp)
  | some p =>
    obtain ⟨as, vs⟩ := p
    rw [e'] at hw
    simp only [Option.map_some, Option.some.injEq] at hw
    obtain ⟨σ, hp, -, -, hpops⟩ := valid_pops_atomsRet hf e' hn hv
    rw [hpar] at hp
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
    rw [hpops, flatMap_atom_pops, hw, List.map_map, List.range'_eq_map_range, List.map_map]
    refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp_apply, words_heap σ hp.2, claimPop, Nat.zero_add]
    congr 2
    funext c
    congr 3
    ring

/-! ## `claim_list_tail` -/

theorem tail_noWit : Stmt.noWitList (Fn.body fn% «claim_list_tail») = true := by decide +kernel

/-- **`claim_list_tail`** called on `[sp, g^e, g^r]`, `r < 17`, pops claims `0 ..< r` of the table at `g^e`: its
dispatch's `claim_list_last__L{r}`'s. -/
theorem tail_pops {r : ℕ} (hr : r < 17) {t : Tree} {sp : E} {e : ℕ} {rets : List E}
    (hn : t.name = "claim_list_tail") (hv : t.Valid coreProgram rd [sp, gen ^ e, gen ^ r] rets) :
    t.pops coreProgram rd = (List.range' 0 r).map (claimPop rd e) := by
  cases t with
  | phantom _ _ => exact hv.elim
  | node f σ bufs ks =>
    obtain rfl : f = "claim_list_tail" := hn
    rw [valid_pops_noWit find_claim_list_tail tail_noWit hv]
    obtain ⟨fn', hf', hp, es, vs, hw, -, -, hk⟩ := hv
    rw [find_claim_list_tail] at hf'
    obtain rfl := Option.some.inj hf'
    rw [claim_list_tail_params] at hp
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hp
    obtain ⟨-, h1, h2⟩ := hp
    have hw2 := walk_dispatch σ [] [.atom (.copy (.n (val% «claim_list_tail» "s1#0")) (.n (val% «claim_list_tail» "d0"))), .atom (.copy (.n (val% «claim_list_tail» "s1#0[1]")) (.n (val% «claim_list_tail» "d1")))] rfl rfl (.n (val% «claim_list_tail» "rest"))
      clNames [.n (val% «claim_list_tail» "state"), .n (val% «claim_list_tail» "blk")] [.n (val% «claim_list_tail» "d0"), .n (val% «claim_list_tail» "d1")] [.n (val% «claim_list_tail» "s1#0"), .n (val% «claim_list_tail» "s1#0[1]")] (i := r) (by simp [clNames]; omega) (by simp [clNames])
      (by rw [h2, gen_pow_eq_ofK])
    rw [claim_list_tail_shape] at hw
    rw [show [Stmt.dispatch (.n (val% «claim_list_tail» "rest")) clNames [.n (val% «claim_list_tail» "state"), .n (val% «claim_list_tail» "blk")] [.n (val% «claim_list_tail» "d0"), .n (val% «claim_list_tail» "d1")], .atom (.copy (.n (val% «claim_list_tail» "s1#0")) (.n (val% «claim_list_tail» "d0"))),
        .atom (.copy (.n (val% «claim_list_tail» "s1#0[1]")) (.n (val% «claim_list_tail» "d1"))), .ret [.n (val% «claim_list_tail» "s1#0"), .n (val% «claim_list_tail» "s1#0[1]")]] = [] ++ Stmt.dispatch (.n (val% «claim_list_tail» "rest")) clNames [.n (val% «claim_list_tail» "state"), .n (val% «claim_list_tail» "blk")]
          [.n (val% «claim_list_tail» "d0"), .n (val% «claim_list_tail» "d1")] :: ([.atom (.copy (.n (val% «claim_list_tail» "s1#0")) (.n (val% «claim_list_tail» "d0"))), .atom (.copy (.n (val% «claim_list_tail» "s1#0[1]")) (.n (val% «claim_list_tail» "d1")))] ⧺ [.ret [.n (val% «claim_list_tail» "s1#0"), .n (val% «claim_list_tail» "s1#0[1]")]])
        from rfl, hw2] at hw
    obtain ⟨rfl, -⟩ := Out.ret.inj hw
    obtain ⟨k, rfl⟩ : ∃ k, ks = [k] := by
      match ks, hk with
      | [k], _ => exact ⟨k, rfl⟩
    obtain ⟨hnk, hvk, -⟩ := hk
    simp only [ite_true] at hvk
    have hvk' : k.Valid coreProgram rd [σ (.n (val% «claim_list_tail» "state")), σ (.n (val% «claim_list_tail» "blk"))] [σ (.n (val% «claim_list_tail» "d0")), σ (.n (val% «claim_list_tail» "d1"))] := hvk
    rw [h1] at hvk'
    rw [Tree.popsKids, Tree.popsKids, List.flatten_cons, List.flatten_nil, List.append_nil]
    exact clLast_pops hr (by rw [hnk]; exact clNames_get hr) hvk'

/-! ## `claim_list_chain` -/

theorem ch_noWit : Stmt.noWitList (Fn.body fn% «claim_list_chain») = true := by decide +kernel

/-- **A valid tree of `claim_list_chain` on `n` claims at `g^eP`, of honest shape,** pops the `n` claims of the table
at `g^eP`. -/
theorem ch_valid_pops {n eP : ℕ} (hn : n < claimBig * bigFramesCap) {t : Tree} {ng : E} {rets : List E}
    (hv : t.Valid coreProgram rd [gen ^ eP, ng, gen ^ (n / 136), gen ^ (n % 136 / 17), gen ^ (n % 17)] rets)
    (hH : chHonest n t) :
    t.pops coreProgram rd = (List.range n).map (claimPop rd eP) := by
  simp only [claimBig, bigFramesCap] at hn
  obtain ⟨σ, ks, rfl, hQ, hcs, -, -⟩ := hH
  obtain ⟨fn0, hf0, hp0, hb⟩ := valid_holds hv
  rw [find_claim_list_chain] at hf0
  obtain rfl := Option.some.inj hf0
  rw [valid_pops_noWit find_claim_list_chain ch_noWit hv]
  obtain ⟨fn', hf', -, es, vs, hw, -, -, hk⟩ := hv
  rw [hcs fn' es vs hf' hw] at hk
  obtain ⟨h12, h13, h14, -, h39, h59⟩ := hQ
  set a := n / 136 with ha
  set b := n % 136 / 17 with hb'
  set r := n % 17 with hr
  have hr17 : r < 17 := Nat.mod_lt _ (by norm_num)
  have h0 : σ (.n (val% «claim_list_chain» "entries_ptr")) = gen ^ eP := by
    rw [ch_param] at hp0
    exact (List.cons.inj hp0).1
  rw [claim_list_chain_shape, holdsList_append] at hb
  have hok := chainBody_ok
  simp only [chainBodyOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hfl, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩,
    -⟩, -⟩, hm67⟩, -⟩, hm84⟩, -⟩, -⟩ := hok
  obtain ⟨hall, -⟩ := holdsList_flat _ (List.all_eq_true.mpr hfl) _ _ hb
  have hat := atoms_of_flat hall
  have h56 : σ (.n (val% «claim_list_chain» "mid_entries")) = gen ^ (eP + 4 * (136 * a)) := by
    rw [monoIs_sound hm67 hat, h0, h12, ← pow_mul, ← pow_add]
    exact congrArg (HPow.hPow gen) (by ring)
  have h73 : σ (.n (val% «claim_list_chain» "d0~9")) = gen ^ (eP + 4 * (136 * a + 17 * b)) := by
    rw [mono2Is_sound hm84 hat, h0, h12, h13, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
    exact congrArg (HPow.hPow gen) (by ring)
  -- the callees
  rw [chCalls] at hk
  obtain ⟨k2, k3, k4, rfl⟩ : ∃ k2 k3 k4, ks = [k2, k3, k4] := by
    have := kidsValid_len hk
    simp only [List.length_cons, List.length_nil] at this
    match ks, this with
    | [k2, k3, k4], _ => exact ⟨k2, k3, k4, rfl⟩
  obtain ⟨hn2', hv2, hn3', hv3, hn4', hv4, -⟩ := hk
  have p2 : k2.pops coreProgram rd = (List.range' 0 (136 * a)).map (claimPop rd eP) := by
    refine grp_pops_entry big_idx big_ok big_wits (M := a) (chain := σ (.n (val% «claim_list_chain» "chain"))) (by omega) hn2'
      (fun ha0 => ?_) (fun ha0 => ?_)
    · rw [ite_eq_left (decide_eq_true ha0)] at hv2
      have hv2' : k2.Valid coreProgram rd [σ (.n (val% «claim_list_chain» "s2#2")), σ (.n (val% «claim_list_chain» "bigs")), σ (.n (val% «claim_list_chain» "chain")), σ (.n (val% «claim_list_chain» "entries_ptr"))] [] := hv2
      rwa [h39, h12, h0] at hv2'
    · rw [ite_eq_right (fun h => (of_decide_eq_true h) ha0)] at hv2
      exact hv2.1
  have p3 : k3.pops coreProgram rd = (List.range' (136 * a) (17 * b)).map (claimPop rd eP) := by
    rw [← Nat.add_zero (136 * a), ← map_claimPop_shift]
    refine grp_pops_entry grp_idx grp_ok grp_wits (M := b) (chain := σ (.n (val% «claim_list_chain» "mid"))) (by omega) hn3'
      (fun hb0 => ?_) (fun hb0 => ?_)
    · rw [ite_eq_left (decide_eq_true hb0)] at hv3
      have hv3' : k3.Valid coreProgram rd [σ (.n (val% «claim_list_chain» "s5#2")), σ (.n (val% «claim_list_chain» "groups")), σ (.n (val% «claim_list_chain» "mid")), σ (.n (val% «claim_list_chain» "mid_entries"))] [] := hv3
      rwa [h59, h13, h56] at hv3'
    · rw [ite_eq_right (fun h => (of_decide_eq_true h) hb0)] at hv3
      exact hv3.1
  have p4 : k4.pops coreProgram rd = (List.range' (136 * a + 17 * b) r).map (claimPop rd eP) := by
    rw [← Nat.add_zero (136 * a + 17 * b), ← map_claimPop_shift]
    have hv4' : k4.Valid coreProgram rd [σ (.n (val% «claim_list_chain» "last")), σ (.n (val% «claim_list_chain» "d0~9")), σ (.n (val% «claim_list_chain» "rest"))] [σ (.n (val% «claim_list_chain» "d0")), σ (.n (val% «claim_list_chain» "d1"))] := hv4
    rw [h73, h14] at hv4'
    exact tail_pops hr17 hn4' hv4'
  rw [Tree.popsKids, Tree.popsKids, Tree.popsKids, Tree.popsKids, p2, p3, p4]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil]
  rw [← List.map_append, ← List.map_append, List.range'_append_1, range'_zero_append, List.range_eq_range',
    show 136 * a + (17 * b + r) = n by omega]

/-! ## `claim_list_digest` -/

theorem cl_noWit : Stmt.noWitList (Fn.body fn% «claim_list_digest») = true := by decide +kernel

/-- **A valid tree of `claim_list_digest` on `n` claims at `g^eP`, of honest shape,** pops the split, then the `n`
claims of the table at `g^eP`. -/
theorem cl_valid_pops {n eP : ℕ} (hn : n < claimBig * bigFramesCap) {t : Tree} {rets : List E}
    (hv : t.Valid coreProgram rd [gen ^ eP, gen ^ n] rets)
    (hH : NodeHonest coreProgram "claim_list_digest" (clQ n) (clCalls n) (clBufs n) (clTs n) t) :
    t.pops coreProgram rd = (if n = 0 then [] else [("signers_split", [gen ^ (n / 136), gen ^ (n % 136 / 17),
      gen ^ (n % 17)])]) ++ (List.range n).map (claimPop rd eP) := by
  obtain ⟨σ, ks, rfl, hQ, hcs, -, hT⟩ := hH
  obtain ⟨fn0, hf0, hp0, -⟩ := valid_holds hv
  rw [find_claim_list_digest] at hf0
  obtain rfl := Option.some.inj hf0
  rw [valid_pops_noWit find_claim_list_digest cl_noWit hv]
  obtain ⟨fn', hf', -, es, vs, hw, -, -, hk⟩ := hv
  rw [hcs fn' es vs hf' hw] at hk
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · simp only [clCalls, ↓reduceIte] at hk
    cases ks with
    | nil => rfl
    | cons _ _ => exact hk.elim
  · obtain ⟨h12, h13, h14⟩ := hQ.2 (by omega)
    have hn1 := hQ.1
    have h0 : σ (.n (val% «claim_list_digest» "entries_ptr")) = gen ^ eP := by
      rw [cl_param] at hp0
      exact (List.cons.inj hp0).1
    rw [clCalls, ite_eq_right (by omega)] at hk
    rw [clCalls, ite_eq_right (by omega)] at hT
    obtain ⟨k1, k2, rfl⟩ : ∃ k1 k2, ks = [k1, k2] := by
      have := kidsValid_len hk
      simp only [List.length_cons, List.length_nil] at this
      match ks, this with
      | [k1, k2], _ => exact ⟨k1, k2, rfl⟩
    obtain ⟨hn1', hv1, hn2', hv2, -⟩ := hk
    have p1 : k1.pops coreProgram rd = [("signers_split", [gen ^ (n / 136), gen ^ (n % 136 / 17), gen ^ (n % 17)])] := by
      have hv1' : k1.Valid coreProgram rd [σ (.n (val% «claim_list_digest» "n_g"))] [σ (.n (val% «claim_list_digest» "bigs")), σ (.n (val% «claim_list_digest» "groups")), σ (.n (val% «claim_list_digest» "rest"))] := hv1
      rw [list_split_pops hn1' hv1', h12, h13, h14]
    have p2 : k2.pops coreProgram rd = (List.range n).map (claimPop rd eP) := by
      have hv2' : k2.Valid coreProgram rd [σ (.n (val% «claim_list_digest» "entries_ptr")), σ (.n (val% «claim_list_digest» "n_g")), σ (.n (val% «claim_list_digest» "bigs")), σ (.n (val% «claim_list_digest» "groups")), σ (.n (val% «claim_list_digest» "rest"))]
          [σ (.n (val% «claim_list_digest» "d0")), σ (.n (val% «claim_list_digest» "d1"))] := hv2
      rw [h0, h12, h13, h14] at hv2'
      exact ch_valid_pops hn hv2' (hT.2.1 rfl)
    rw [Tree.popsKids, Tree.popsKids, Tree.popsKids, p1, p2, ite_eq_right (by omega)]
    simp only [List.flatten_cons, List.flatten_nil, List.append_nil]

end
end LeanVM.Guest.B1.Digest
