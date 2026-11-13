/-
  LeanVM.Guest.B1.Main.KidsAt

  `main`'s children loop `main_loop4` in the uniform placed form: each child's block, its callees
  after the rest of the loop.
-/

module

public import LeanVM.Guest.B1.Main.KidBlockC
public import LeanVM.Guest.B1.Main.KidCoverAt
public import LeanVM.Guest.B1.Da.AtBase
public import LeanVM.Guest.Data.NameStrings

/-!
# The children, placed

`KidH`: a child's honest data (its counts, its base `written[c]`, its two claim lists' digests, its
DA digest, its deferred claim's cells), and what it determines: the statement's digest `pi`.
`KidOkC`: what child `c` needs of the caller's words `Lin` (the running counts, the statement's
digest in `child_pi_table`, the DA digest in `da_digests`, the deferred cells) and of its callees
not lifted here (the two `child_claim_list_digest` calls and `verify_sub`, as `CompleteAtD`
hypotheses).

`l5_stepAt`: child `c` and the rest of the loop; `l5_completeAt`: `main_loop4` from every counter
`c < nk`, by induction from the end. A loop helper's tail sits right after its frame, its
callees after the tail (`relAtIn_of_walk_loop`).
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (gen)
open LeanVM.Guest.B1.Digest LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1.Da (SlOk slEvs_holds limb0_gen_pow_mul exists_of_length_succ fn_name_of_find)
open LeanVM.Guest.B1 (CompleteAtD Returns Kid OutsOk CallsMatch RegionsOk outRegion DisjL Within
  disj_append disj_nil kidsFromIn_of_kidsD regionsOk_of within_append LowDef)

@[expose] public section

/-! ## A child's honest data -/

/-- **A child's honest data.** -/
structure KidH where
  ex : ℕ
  es : ℕ
  base : E
  cx : E × E
  cs : E × E
  da : E × E
  defer : List E

namespace KidH

/-- The child's statement's digest. -/
def pi (k : KidH) (s0 s1 : E) : E × E :=
  digestHalves (keccak256
    (stmtBytes [s0, s1, k.cx.1, k.cx.2, k.cs.1, k.cs.2, k.da.1, k.da.2] k.defer))

end KidH

variable (fs : String → ℕ) (cert : String → V → ℕ)

/-- **What child `c` needs**: its counts' bounds, the caller's words (the
running counts at `g^W`, the DA digest at `g^(D + 2c)`, the statement's digest at `g^(Pi + 2c)`,
the deferred cells at `g^(Cr + 24c)`) and their addresses in `Lin`, and its callees
`child_claim_list_digest` (twice) and `verify_sub` complete reading `Lin`. -/
structure KidOkC (Lin : Layout) (W D Pi Cr : ℕ) (lxt cover lxs lst spc lss s0 s1 gsq cfresh : E)
    (c : ℕ) (k : KidH) : Prop where
  ex_lt : k.ex < 2 ^ 23
  es_lt : k.es < 2 ^ 23
  defer_len : k.defer.length = 24
  mem : ∀ rd, MemL rd Lin →
    LoadHolds rd (gen ^ W) c k.base ∧
    LoadHolds rd (gen ^ W) (c + 1) (k.base * (gen ^ k.ex * gen ^ k.es)) ∧
    LoadHolds rd (gen ^ D) (2 * c) k.da.1 ∧
    LoadHolds rd (gen ^ D) (2 * c + 1) k.da.2 ∧
    LoadHolds rd (gen ^ Pi) (2 * c) (k.pi s0 s1).1 ∧
    LoadHolds rd (gen ^ Pi) (2 * c + 1) (k.pi s0 s1).2 ∧
    ReadsAt rd (gen ^ (Cr + 24 * c)) k.defer
  reg : RegionL Lin (W + c) ∧ RegionL Lin (W + c + 1) ∧ RegionL Lin (D + 2 * c) ∧
    RegionL Lin (D + 2 * c + 1) ∧ RegionL Lin (Pi + 2 * c) ∧ RegionL Lin (Pi + 2 * c + 1)
  hX : CompleteAtD fs cert 23 "child_claim_list_digest" Lin [lxt, cover, k.base, lxs, gen ^ k.ex]
    (Returns [k.cx.1, k.cx.2])
  hS : CompleteAtD fs cert 23 "child_claim_list_digest" Lin
    [lst, spc, k.base * gen ^ k.ex, lss, gen ^ k.es] (Returns [k.cs.1, k.cs.2])
  hV : CompleteAtD fs cert 20 "verify_sub" Lin
    [(k.pi s0 s1).1, (k.pi s0 s1).2, s0, s1, gsq, cfresh * gen ^ (24 * c)] (Returns [])

theorem gen_sq' (j : ℕ) : gen ^ j * gen ^ j = gen ^ (2 * j) := by rw [← pow_add, two_mul]

/-- A statement of `main_loop4`'s block: an atom or a call. -/
def l5Kind : Stmt → Bool
  | .atom _ => true
  | .call .. => true
  | _ => false

set_option maxRecDepth 100000 in
theorem l5_kinds : l5Pre.all l5Kind = true := by decide +kernel

theorem l5Pre_straight : (l5Pre ++ [l5Tail]).all Main.Stmt.straight = true := by decide

theorem l5Body_split : l5Body = (l5Pre ++ [l5Tail]) ++ [.ret []] := by
  simp [l5Body]

theorem find_l5 : coreProgram.find? name% «main_loop4» = some (coreProgram.getD idx% «main_loop4»
    default) :=
  find_of_idx l5_idx

theorem l5_loop : coreProgram.loop name% «main_loop4» = true := by
  rw [Program.loop_of_find? find_l5, Fn.loop, l5_body, fn_name_of_find find_l5]
  simp [l5Tail]

set_option maxRecDepth 20000 in
/-- **One child of `main_loop4`, placed**: child `c` and the rest of the loop. -/
theorem l5_stepAt {Lin : Layout} {W D Pi Cr nk c : ℕ}
    {lxt cover lxs lst spc lss s0 s1 gsq cfresh : E} {k : KidH}
    (hnk : nk < 2 ^ 34) (hc : c + 1 ≤ nk)
    (hk : KidOkC fs cert Lin W D Pi Cr lxt cover lxs lst spc lss s0 s1 gsq cfresh c k)
    (htail : c + 1 < nk → CompleteAtD fs cert 23 name% «main_loop4» Lin
      [gen ^ (c + 1), gen ^ nk, gen ^ W, lxt, cover, lxs, lst, spc, lss, gen ^ Cr,
        gen ^ D, s0, s1, gen ^ Pi, gsq, cfresh] (Returns [])) :
    CompleteAtD fs cert 23 name% «main_loop4» Lin
      [gen ^ c, gen ^ nk, gen ^ W, lxt, cover, lxs, lst, spc, lss, gen ^ Cr,
        gen ^ D, s0, s1, gen ^ Pi, gsq, cfresh] (Returns []) := by
  intro fp
  -- the rest of the loop
  obtain ⟨nt, Lt, hWt, hDt, hRt⟩ : ∃ nt Lt, Within Lt (fp + fs name% «main_loop4») nt ∧ DisjL Lt ∧
      ∀ rd, LowDef 23 rd → MemL rd (Lt ++ Lin) →
        if decide (c + 1 ≠ nk) = true then
          RelAtIn coreProgram fs cert rd (RegionL Lin) (RegionL []) (fp + fs name% «main_loop4») nt
              name% «main_loop4»
            [gen ^ (c + 1), gen ^ nk, gen ^ W, lxt, cover, lxs, lst, spc, lss, gen ^ Cr,
              gen ^ D, s0, s1, gen ^ Pi, gsq, cfresh] []
        else nt = fs name% «main_loop4» := by
    by_cases hlast : c + 1 = nk
    · exact ⟨fs name% «main_loop4», [], fun q hq => by simp at hq, List.Pairwise.nil,
                                                         fun _ _ _ => by
        simp [hlast]⟩
    · obtain ⟨nt, Lt, rt, Lot, ⟨rfl, rfl⟩, hW, hD, hR⟩ := htail (by omega) (fp + fs
                                                                      name% «main_loop4»)
      refine ⟨nt, Lt, by simpa using hW, by simpa using hD, fun rd hl hm => ?_⟩
      simp only [ne_eq, hlast, not_false_eq_true, decide_true, ↓reduceIte]
      exact hR rd hl (by simpa using hm)
  set P1 := fp + fs name% «main_loop4» + nt with hP1
  -- the callees
  let ks : List Kid :=
    [⟨"child_claim_list_digest", true, [lxt, cover, k.base, lxs, gen ^ k.ex], Lin,
        Returns [k.cx.1, k.cx.2]⟩,
      ⟨"child_claim_list_digest", true, [lst, spc, k.base * gen ^ k.ex, lss, gen ^ k.es], Lin,
        Returns [k.cs.1, k.cs.2]⟩,
      ⟨"statement_digest", true, [s0, s1, k.cx.1, k.cx.2, k.cs.1, k.cs.2, k.da.1, k.da.2,
        gen ^ Cr * gen ^ (24 * c)], Lin, Returns [(k.pi s0 s1).1, (k.pi s0 s1).2]⟩,
      ⟨"verify_sub", true, [(k.pi s0 s1).1, (k.pi s0 s1).2, s0, s1, gsq,
        cfresh * gen ^ (24 * c)], Lin, Returns []⟩]
  have hok : ∀ kd ∈ ks, kd.taken = true → CompleteAtD fs cert 23 kd.f kd.Lin kd.args kd.Out := by
    intro kd hkd _
    simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hkd
    rcases hkd with rfl | rfl | rfl | rfl
    · exact hk.hX
    · exact hk.hS
    · refine statement_completeAt fs cert fun rd hm => ?_
      obtain ⟨-, -, -, -, -, -, hdef⟩ := hk.mem rd hm
      exact ⟨k.defer, hk.defer_len, by rw [← pow_add]; exact hdef, rfl⟩
    · exact LeanVM.Guest.B1.CompleteAtD.mono hk.hV (by norm_num)
  obtain ⟨Nk, Lk, outs, hoo, hW, hD, -, hKids⟩ :=
    kidsFromIn_of_kidsD (fs := fs) (cert := cert) 23 ks hok P1
  have hl0 : outs.length = 4 := hoo.length
  obtain ⟨o1, t1, rfl, hl1⟩ := exists_of_length_succ hl0
  obtain ⟨o2, t2, rfl, hl2⟩ := exists_of_length_succ hl1
  obtain ⟨o3, t3, rfl, hl3⟩ := exists_of_length_succ hl2
  obtain ⟨o4, t4, rfl, hl4⟩ := exists_of_length_succ hl3
  obtain rfl := List.eq_nil_of_length_eq_zero hl4
  obtain ⟨h1, h2, h3, h4, -⟩ := hoo
  -- the layout
  refine ⟨fs name% «main_loop4» + nt + Nk, Lt ++ Lk, [], [], ⟨rfl, rfl⟩, ?_,
    by rw [List.nil_append]; exact disj_append hDt hD hWt hW (by omega), fun rd hlow hm => ?_⟩
  · rw [List.nil_append, within_append]
    exact ⟨hWt.mono (by omega) (by omega), hW.mono (by omega) (by omega)⟩
  simp only [List.nil_append] at hm
  obtain ⟨hm1, hLin⟩ := Main.memL_append.mp hm
  obtain ⟨hmt, hLk⟩ := Main.memL_append.mp hm1
  have ht := hRt rd hlow (Main.memL_append.mpr ⟨hmt, hLin⟩)
  obtain ⟨hb0, hb1, hd0, hd1, hpi0, hpi1, -⟩ := hk.mem rd hLin
  obtain ⟨rW0, rW1, rD0, rD1, rPi0, rPi1⟩ := hk.reg
  -- the block
  have hV := l5_core (rd := rd) (c := c) (N := gen ^ nk) (written := gen ^ W) (lxt := lxt)
    (cover := cover) (lxs := lxs) (lst := lst) (spc := spc) (lss := lss) (carried := gen ^ Cr)
    (dadig := gen ^ D) (s0 := s0) (s1 := s1) (cpi := gen ^ Pi) (gsq := gsq)
    (cfresh := cfresh) (cx0 := k.cx.1) (cx1 := k.cx.2) (cs0 := k.cs.1) (cs1 := k.cs.2)
    (d0 := k.da.1) (d1 := k.da.2) (p0 := (k.pi s0 s1).1) (p1 := (k.pi s0 s1).2)
    hlow hk.ex_lt hk.es_lt
    (by rw [loadHolds_mul_gen_pow, Nat.add_zero]; exact hb0)
    (by rw [gen_sq', loadHolds_mul_gen_pow, Nat.add_zero]; exact hd0)
    (by rw [gen_sq', loadHolds_mul_gen_pow]; exact hd1)
    (by rw [gen_sq', loadHolds_mul_gen_pow, Nat.add_zero]; exact hpi0)
    (by rw [gen_sq', loadHolds_mul_gen_pow]; exact hpi1)
    (by rw [loadHolds_mul_gen_pow]; exact hb1)
  set args : List E := [gen ^ c, gen ^ nk, gen ^ W, lxt, cover, lxs, lst, spc, lss, gen ^ Cr,
    gen ^ D, s0, s1, gen ^ Pi, gsq, cfresh] with hargs
  set σ := l5σ rd args (l5W k.ex k.es k.cx.1 k.cx.2 k.cs.1 k.cs.2 (k.pi s0 s1).1 (k.pi s0 s1).2)
    with hσ
  have pr : ∀ i (hi : i < 16), σ (.n i) = args.getD i 0 := hV.par
  -- the path
  have hw' := Main.walk_straight σ [] (l5Pre ++ [l5Tail]) l5Pre_straight
  rw [← l5Body_split, l5Body] at hw'
  rw [← l5_body] at hw'
  obtain ⟨hpd, hpa, hpad, hpc⟩ := Main.straight_parts σ _ l5Pre_straight
  have hal : allocs σ ((l5Pre ++ [l5Tail]).flatMap (Main.slEvs σ)) = [] := by
    rw [hpa, show (l5Pre ++ [l5Tail]).filterMap Main.Stmt.allocSz = [] from rfl]; rfl
  have h59 : decide (σ (.n 53) ≠ 0) = decide (c + 1 ≠ nk) := by
    rw [hV.v59]
    refine decide_eq_decide.mpr ⟨fun h he => h (by rw [he]; exact e_add_eq_zero_iff.mpr rfl),
      fun h he => h ?_⟩
    exact gen_pow_inj' (by omega) (by omega) (e_add_eq_zero_iff.mp he)
  have hcalls : calls ((l5Pre ++ [l5Tail]).flatMap (Main.slEvs σ)) =
      [⟨"child_claim_list_digest", [.n 3, .n 4, .n 17, .n 5, .n 18], [.n 23, .n 24], true⟩,
        ⟨"child_claim_list_digest", [.n 6, .n 7, .n 25, .n 8, .n 19], [.n 26, .n 27], true⟩,
        ⟨"statement_digest", [.n 11, .n 12, .n 23, .n 24, .n 26, .n 27, .n 36, .n 37, .n 33],
          [.n 38, .n 39], true⟩,
        ⟨"verify_sub", [.n 38, .n 39, .n 11, .n 12, .n 14, .n 48], [], true⟩] ++
      [⟨name% «main_loop4», [.n 55, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10,
          .n 11,
        .n 12, .n 13, .n 14, .n 15], [], decide (c + 1 ≠ nk)⟩] := by
    rw [hpc, show (l5Pre ++ [l5Tail]).filterMap Main.Stmt.callS =
      [(none, "child_claim_list_digest", [.n 3, .n 4, .n 17, .n 5, .n 18], [.n 23, .n 24]),
        (none, "child_claim_list_digest", [.n 6, .n 7, .n 25, .n 8, .n 19], [.n 26, .n 27]),
        (none, "statement_digest", [.n 11, .n 12, .n 23, .n 24, .n 26, .n 27, .n 36, .n 37, .n 33],
          [.n 38, .n 39]),
        (none, "verify_sub", [.n 38, .n 39, .n 11, .n 12, .n 14, .n 48], []),
        (some (.n 53), name% «main_loop4», [.n 55, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8,
            .n 9,
          .n 10, .n 11, .n 12, .n 13, .n 14, .n 15], [])] from rfl]
    simp only [List.map_cons, List.map_nil, Main.mkCall, h59, List.cons_append, List.nil_append]
  have hev : ∀ e ∈ (l5Pre ++ [l5Tail]).flatMap (Main.slEvs σ), e.Holds rd σ := by
    refine slEvs_holds fun s hs => ?_
    rcases List.mem_append.mp hs with hs | hs
    · have hk' := List.all_eq_true.mp l5_kinds s hs
      match s, hk' with
      | .atom a, _ => exact hV.atoms a (Da.mem_atomsIn hs)
      | .call .., _ => trivial
      | .callIf .., hk' => simp [l5Kind] at hk'
      | .ite .., hk' => simp [l5Kind] at hk'
      | .match_ .., hk' => simp [l5Kind] at hk'
      | .dispatch .., hk' => simp [l5Kind] at hk'
      | .ret _, hk' => simp [l5Kind] at hk'
    · rw [List.mem_singleton] at hs
      subst hs
      show IsInK (σ (.n 53))
      rw [hV.v59]; exact gen_pow_add_isInK _ _
  have hparams : (coreProgram.getD idx% «main_loop4» default).params.map σ = args := by
    rw [l5_params]
    refine List.ext_getElem (by simp [hargs]) fun i h1 h2 => ?_
    simp only [List.getElem_map, List.getElem_range]
    rw [pr i (by simpa using h1), List.getD_eq_getElem _ _ h2]
  have h := relAtIn_of_walk_loop (P := coreProgram) (fs := fs) (cert := cert) (σ := σ) (rd := rd)
    (R := RegionL Lin) (D := RegionL []) (Rt := RegionL Lin) (Dt := RegionL []) (fp := fp)
    (m := nt) (N := Nk) (args := args)
    (Dk := fun i => (fun _ => False) i ∨ outRegion ks [o1, o2, o3, o4] i)
    coreProgram_wf find_l5 l5_loop hparams hw' rfl hev hcalls
    (by
      by_cases hlast : c + 1 = nk
      · simpa [hlast] using ht
      · simp only [ne_eq, hlast, not_false_eq_true, decide_true, ↓reduceIte] at ht ⊢
        rw [show [V.n 55, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10, .n 11,
          .n 12, .n 13, .n 14, .n 15].map σ = [σ (.n 55), σ (.n 1), σ (.n 2),
          σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 7), σ (.n 8), σ (.n 9), σ (.n 10),
          σ (.n 11), σ (.n 12), σ (.n 13), σ (.n 14), σ (.n 15)] from rfl,
          hV.v61, pr 1 (by omega), pr 2 (by omega), pr 3 (by omega), pr 4 (by omega),
          pr 5 (by omega), pr 6 (by omega), pr 7 (by omega), pr 8 (by omega), pr 9 (by omega),
          pr 10 (by omega), pr 11 (by omega), pr 12 (by omega), pr 13 (by omega), pr 14 (by omega),
          pr 15 (by omega)]
        exact ht)
    (by rw [hal, hpd, show (l5Pre ++ [l5Tail]).filterMap Main.Stmt.allocSz = [] from rfl]; rfl)
    (fun q hq => by
      rw [hpad, show (l5Pre ++ [l5Tail]).filterMap Main.Stmt.addrS = [] from rfl] at hq
      simp at hq)
    ?_ (fun i hi => Or.inl hi) ?_ (fun i hi => by obtain ⟨q, hq, -⟩ := hi; simp at hq)
  · rw [hal] at h
    simpa using h
  · rw [hal]
    refine hKids rd σ _ _ _ ?_ hlow hLk ?_ (regionsOk_of fun kd hkd _ i hi => ?_)
    · refine ⟨rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩, rfl, rfl,
        fun _ => ⟨?_, ?_⟩, rfl, rfl, fun _ => ⟨?_, ?_⟩, trivial⟩
      · show [σ (.n 3), σ (.n 4), σ (.n 17), σ (.n 5), σ (.n 18)] = _
        rw [pr 3 (by omega), pr 4 (by omega), hV.v17, pr 5 (by omega), hV.v18]; rfl
      · rw [(h1 rfl).1]; show [σ (.n 23), σ (.n 24)] = _; rw [hV.v29, hV.v30]
      · show [σ (.n 6), σ (.n 7), σ (.n 25), σ (.n 8), σ (.n 19)] = _
        rw [pr 6 (by omega), pr 7 (by omega), hV.v31, pr 8 (by omega), hV.v19]
        rfl
      · rw [(h2 rfl).1]; show [σ (.n 26), σ (.n 27)] = _; rw [hV.v32, hV.v33]
      · show [σ (.n 11), σ (.n 12), σ (.n 23), σ (.n 24), σ (.n 26), σ (.n 27), σ (.n 36),
          σ (.n 37), σ (.n 33)] = _
        rw [pr 11 (by omega), pr 12 (by omega), hV.v29, hV.v30, hV.v32, hV.v33, hV.v42, hV.v43,
          hV.v39]
        rfl
      · rw [(h3 rfl).1]; show [σ (.n 38), σ (.n 39)] = _; rw [hV.v44, hV.v45]
      · show [σ (.n 38), σ (.n 39), σ (.n 11), σ (.n 12), σ (.n 14), σ (.n 48)] = _
        rw [hV.v44, hV.v45, pr 11 (by omega), pr 12 (by omega), pr 14 (by omega), hV.v54]
        rfl
      · rw [(h4 rfl).1]; rfl
    · intro q hq
      simp only [B1.Kid.lins, ks, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_append] at hq
      rcases hq with hq | hq | hq | hq
      all_goals exact hLin q hq
    · simp only [ks, List.mem_cons, List.not_mem_nil, or_false] at hkd
      rcases hkd with rfl | rfl | rfl | rfl
      all_goals exact Or.inl (Or.inl hi)
  · intro A hA
    rw [B1.loadAddrs_straight σ _ l5Pre_straight,
      show (l5Pre ++ [l5Tail]).filterMap B1.Stmt.loadS =
        [(.n 16, 0), (.n 35, 0), (.n 35, 1), (.n 41, 0), (.n 42, 1), (.n 50, 1)] from rfl] at hA
    simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hA
    rw [hal]
    have hW' : ∀ e, (gen ^ W * gen ^ c).limb 0 * addressOfIndex e = addressOfIndex (W + c + e) :=
        fun e => by
      rw [← pow_add, limb0_gen_pow_mul]
    have hsq : ∀ B e, (gen ^ B * (gen ^ c * gen ^ c)).limb 0 * addressOfIndex e = addressOfIndex (B
        + 2 * c + e) :=
      fun B e => by rw [gen_sq', ← pow_add, limb0_gen_pow_mul]
    rcases hA with rfl | rfl | rfl | rfl | rfl | rfl
    · refine ⟨W + c + 0, ?_, Or.inr (Or.inl rW0)⟩
      rw [hV.v16]; exact hW' 0
    · refine ⟨D + 2 * c + 0, ?_, Or.inr (Or.inl rD0)⟩
      rw [hV.v41]; exact hsq D 0
    · refine ⟨D + 2 * c + 1, ?_, Or.inr (Or.inl rD1)⟩
      rw [hV.v41]; exact hsq D 1
    · refine ⟨Pi + 2 * c + 0, ?_, Or.inr (Or.inl rPi0)⟩
      rw [hV.v47]; exact hsq Pi 0
    · refine ⟨Pi + 2 * c + 1, ?_, Or.inr (Or.inl rPi1)⟩
      rw [hV.v48]; exact hsq Pi 1
    · refine ⟨W + c + 1, ?_, Or.inr (Or.inl rW1)⟩
      rw [hV.v56]; exact hW' 1

/-- **`main_loop4` is complete, placed**, from every counter `c < nk`, when every child `c < nk` is
(`KidOkC`). -/
theorem l5_completeAt {Lin : Layout} {W D Pi Cr nk : ℕ}
    {lxt cover lxs lst spc lss s0 s1 gsq cfresh : E} {kid : ℕ → KidH}
    (hnk : nk < 2 ^ 34)
    (hk : ∀ c < nk, KidOkC fs cert Lin W D Pi Cr lxt cover lxs lst spc lss s0 s1 gsq cfresh c
      (kid c)) :
    ∀ c < nk, CompleteAtD fs cert 23 name% «main_loop4» Lin
      [gen ^ c, gen ^ nk, gen ^ W, lxt, cover, lxs, lst, spc, lss, gen ^ Cr,
        gen ^ D, s0, s1, gen ^ Pi, gsq, cfresh] (Returns []) := by
  have key : ∀ t c, c + 1 + t = nk → CompleteAtD fs cert 23 name% «main_loop4» Lin
      [gen ^ c, gen ^ nk, gen ^ W, lxt, cover, lxs, lst, spc, lss, gen ^ Cr,
        gen ^ D, s0, s1, gen ^ Pi, gsq, cfresh] (Returns []) := by
    intro t
    induction t with
    | zero =>
      intro c hc
      exact l5_stepAt fs cert hnk (by omega) (hk c (by omega)) fun h => absurd h (by omega)
    | succ t ih =>
      intro c hc
      exact l5_stepAt fs cert hnk (by omega) (hk c (by omega)) fun _ => ih (c + 1) (by omega)
  intro c hc
  exact key (nk - c - 1) c (by omega)

end
end LeanVM.Guest.B1.Main
