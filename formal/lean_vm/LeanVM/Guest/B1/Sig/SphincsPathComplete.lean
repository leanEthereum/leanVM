/-
  LeanVM.Guest.B1.Sig.SphincsPathComplete

  `sp_path` (`lean_ethereum.py:3913-3933` at leanVM main 40f877dc) is complete: each level's children
  hinted in the order of the leaf's bit, the root is the tree's fold of the siblings; with a level
  of any tree (the hinted pair, `is_child`, an address, the node's hash) complete.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsSoundPath
public import LeanVM.Guest.B1.Sig.MerkleComplete

/-!
# `sp_path`, complete

* `Completes.withAtoms`, `Completes.withExt`: a completion's valuation satisfies the block's atoms
  and extends the start;
* `pairNode_complete`: a level, its children `mPair bt cur sib` hinted (under any name), its address
  any sequential block whose value is canonical;
* `sPath_complete`: a path, the siblings `sib` read back (`sPathSib`), the root `pFold` of
  `pNodeE`, canonical.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-- A hash's first output cell is canonical. -/
theorem canon_hcellFst (cs : List E) : IsCanonical128 (hcell cs).1 := by
  simp [IsCanonical128, hcell, digestHalves]

/-- A completion's valuation satisfies the block's atoms. -/
theorem Completes.withAtoms {lo hi : Nat} {ss : List Stmt} {σ : Val} {P : Val → Prop}
    (hs : atomsOnly ss = true) (h : Completes C rd lo hi ss σ P) :
    Completes C rd lo hi ss σ (fun σ' => P σ' ∧ AtomsHold rd σ' ss) :=
  let ⟨σ', he, hp, hh⟩ := h
  ⟨σ', he, ⟨hp, atomsHold_of_holdsList hs (hh True (fun _ => True) trivial)⟩, hh⟩

/-- A completion's valuation extends the start. -/
theorem Completes.withExt {lo hi : Nat} {ss : List Stmt} {σ : Val} {P : Val → Prop}
    (h : Completes C rd lo hi ss σ P) :
    Completes C rd lo hi ss σ (fun σ' => P σ' ∧ Ext lo hi σ σ') :=
  let ⟨σ', he, hp, hh⟩ := h
  ⟨σ', he, ⟨hp, he⟩, hh⟩

/-- A sequential block, then a block (`Completes.seq`, without `CompleteKit`'s imports). -/
theorem Completes.seqThen {lo m hi : Nat} {xs ys : List Stmt} {σ : Val} {Q : Val → Prop}
    (hs : SeqOK lo xs m) (hhi : m ≤ hi)
    (h : ∀ σ', Ext lo m σ σ' → AtomsHold rd σ' xs → Completes C rd m hi ys σ' Q) :
    Completes C rd lo hi (xs ++ ys) σ Q :=
  Completes.append hs.le hhi hs.numBelow (seq_completes hs σ) h

/-- **`is_child` holds** of children hinted in the order of the bit. -/
theorem isChild_check {σ : Val} {cur bit : V} {x : Nat} {bt : Bool} {sib : E}
    (h0 : σ (.n x) = (mPair bt (σ cur) sib).1) (h1 : σ (.n (x + 1)) = (mPair bt (σ cur) sib).2)
    (hb : σ bit = if bt then 1 else 0) (e0 : σ (.n (x + 2)) = σ cur + σ (.n x))
    (e1 : σ (.n (x + 3)) = σ (.n x) + σ (.n (x + 1))) :
    (Atom.mul (.n (x + 2)) bit (.n (x + 3))).Holds rd σ := by
  show σ (.n (x + 2)) = σ bit * σ (.n (x + 3))
  rw [e0, e1, h0, h1, hb]
  cases bt
  · simp [mPair, e_add_self]
  · simp [mPair, add_comm]

/-- The siblings read back from children hinted in the order of the bit. -/
theorem siblingOf_mPair {σ : Val} {bit : V} {x : Nat} {bt : Bool} {node sib : E}
    (hb : σ bit = if bt then 1 else 0) (h0 : σ (.n x) = (mPair bt node sib).1)
    (h1 : σ (.n (x + 1)) = (mPair bt node sib).2) : siblingOf σ bit x = sib := by
  unfold siblingOf
  rw [hb, h0, h1]
  cases bt <;> simp [mPair]

/-- **A node's hash completes** (`kNode`, `pad_tail=1`): the padding's three cells and the last
byte's constant set, then the `KECCAK` of canonical inputs. -/
theorem kNode_complete {pad : Nat} {pp a0 adr k0 k1 : V} {y : Nat} (σ : Val) (hp : PadOK σ pad)
    (hpy : pad + 5 ≤ y) (hin : ∀ v ∈ [pp, a0, adr, k0, k1], NBv y v ∧ IsCanonical128 (σ v)) :
    Completes C rd y (kNode pad pp a0 adr k0 k1 y).2.1 (kNode pad pp a0 adr k0 k1 y).1 σ
      (fun _ => True) := by
  have hs : SeqOK y [cst y (word 1 0 0), cst (y + 1) (word 0 0 0), cst (y + 2) (word 0 0 0),
      cst (y + 3) (word (2 ^ 63) 0 0)] (y + 4) := ⟨rfl, rfl, rfl, rfl, rfl⟩
  show Completes C rd y (y + 5) ([cst y (word 1 0 0), cst (y + 1) (word 0 0 0),
    cst (y + 2) (word 0 0 0), cst (y + 3) (word (2 ^ 63) 0 0)] ++
    [kecS [pp, a0, adr, k0, k1, .n y, .n (y + 1), .n (y + 2), .n (y + 3), .n (pad + 1),
      .n (pad + 2), .n (pad + 3), .n (pad + 4)] (runV (y + 4) 1) false false]) σ _
  refine Completes.seqThen hs (by omega) (fun σ1 he1 hA1 => ?_)
  have hag : AgreeBelow y σ σ1 := he1.agree
  have hp1 : PadOK σ1 pad := hp.congr hpy hag
  obtain ⟨q0, q1, q2, q3, q4⟩ := hp1
  have c0 : σ1 (.n y) = word 1 0 0 := hA1.atom (a := .const _ _) (by simp [cst])
  have c1 : σ1 (.n (y + 1)) = word 0 0 0 := hA1.atom (a := .const _ _) (by simp [cst])
  have c2 : σ1 (.n (y + 2)) = word 0 0 0 := hA1.atom (a := .const _ _) (by simp [cst])
  have c3 : σ1 (.n (y + 3)) = word (2 ^ 63) 0 0 := hA1.atom (a := .const _ _) (by simp [cst])
  have hv : ∀ v ∈ [pp, a0, adr, k0, k1], NBv y v ∧ IsCanonical128 (σ1 v) := fun v hv' =>
    ⟨(hin v hv').1, by rw [hag.apply (hin v hv').1]; exact (hin v hv').2⟩
  have e0 := hv pp (by simp)
  have e1 := hv a0 (by simp)
  have e2 := hv adr (by simp)
  have e3 := hv k0 (by simp)
  have e4 := hv k1 (by simp)
  have hk := kecS_complete (C := C) (rd := rd) σ1 (o := y + 4)
    (ins := [pp, a0, adr, k0, k1, .n y, .n (y + 1), .n (y + 2), .n (y + 3), .n (pad + 1),
      .n (pad + 2), .n (pad + 3), .n (pad + 4)]) (.inl rfl) rfl
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro v (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals first
        | exact e0.1.mono' (by omega) | exact e1.1.mono' (by omega) | exact e2.1.mono' (by omega)
        | exact e3.1.mono' (by omega) | exact e4.1.mono' (by omega) | exact ⟨_, by omega, rfl⟩)
    (fun c => by
      fin_cases c <;> simp only [cells13, List.map_cons, List.map_nil] <;>
        first
        | exact e0.2 | exact e1.2 | exact e2.2 | exact e3.2 | exact e4.2
        | (simp only [List.getD_cons_succ, List.getD_cons_zero]
           first
           | (rw [c0]; exact canon_word _ _) | (rw [c1]; exact canon_word _ _)
           | (rw [c2]; exact canon_word _ _) | (rw [c3]; exact canon_word _ _)
           | (rw [q1]; exact canon_zero) | (rw [q2]; exact canon_zero)
           | (rw [q3]; exact canon_zero) | (rw [q4]; exact canon_zero)))
    false false
  exact hk.mono le_rfl (by omega) fun _ _ => trivial

/-- **A level of a tree completes**: its children hinted at `x` in the order of the bit `bt`
(`mPair bt cur sib`), `is_child`, its address `addr` (a sequential block from `x + 4` whose value
`adr` is canonical), then the node's 80-byte hash from `y`. -/
theorem pairNode_complete (name : String) {pad : Nat} {pp a0 cur bit adr : V} {x y : Nat}
    {addr : List Stmt} (σ : Val) (hp : PadOK σ pad) (hpx : pad + 5 ≤ x)
    (hpp : NBv x pp) (ha0 : NBv x a0) (hbit : NBv x bit) (hcur : NBv x cur)
    (hseq : SeqOK (x + 4) addr y) (hadr : NBv y adr)
    {bt : Bool} (hbv : σ bit = if bt then 1 else 0) {sib : E} (hsib : IsCanonical128 sib)
    (hcc : IsCanonical128 (σ cur)) (hppc : IsCanonical128 (σ pp)) (ha0c : IsCanonical128 (σ a0))
    (hac : ∀ σ', AgreeBelow x σ σ' → AtomsHold rd σ' addr → IsCanonical128 (σ' adr)) :
    Completes C rd x (y + 5)
      ([hintW name [.n x, .n (x + 1)]] ++ isChildS cur (.n x) (.n (x + 1)) bit (x + 2) ++ addr ++
        (kNode pad pp a0 adr (.n x) (.n (x + 1)) y).1) σ
      (fun σ' => AgreeBelow x σ σ' ∧ σ' (.n x) = (mPair bt (σ cur) sib).1 ∧
        σ' (.n (x + 1)) = (mPair bt (σ cur) sib).2) := by
  have hle := hseq.le
  set kids := mPair bt (σ cur) sib with hkids
  set g : Nat → E := fun j => if j = 0 then kids.1 else kids.2 with hg
  set σr := updRun σ x 2 g with hσr
  have tk : ∀ v, NBv x v → σr v = σ v := fun v hv => updRun_below σ x 2 g hv
  have hk0 : σr (.n x) = kids.1 := by
    have := updRun_at σ x 2 g (j := 0) (by norm_num); rwa [Nat.add_zero] at this
  have hk1 : σr (.n (x + 1)) = kids.2 := updRun_at σ x 2 g (j := 1) (by norm_num)
  have hpc : IsCanonical128 kids.1 ∧ IsCanonical128 kids.2 := by
    cases bt <;> simp [hkids, mPair, hsib, hcc]
  refine Completes.reload ((updRun_ext σ x 2 g).mono le_rfl (by omega)) ?_
  have hsplit : [hintW name [.n x, .n (x + 1)]] ++ isChildS cur (.n x) (.n (x + 1)) bit (x + 2) ++
      addr ++ (kNode pad pp a0 adr (.n x) (.n (x + 1)) y).1 =
      [hintW name [.n x, .n (x + 1)]] ++ ([addS (.n (x + 2)) cur (.n x),
        addS (.n (x + 3)) (.n x) (.n (x + 1))] ++ ([mulS (.n (x + 2)) bit (.n (x + 3))] ++
        (addr ++ (kNode pad pp a0 adr (.n x) (.n (x + 1)) y).1))) := by
    simp [isChildS]
  rw [hsplit]
  refine Completes.append (m := x + 2) (by omega) (by omega)
    (by rw [valsList_hint]; exact .cons ⟨x, by omega, rfl⟩ (.cons ⟨x + 1, by omega, rfl⟩ (.nil _)))
    (hintKeep_complete σr _ _ _ _) (fun σ1 he1 hp1 => ?_)
  subst hp1
  have hs2 : SeqOK (x + 2) [addS (.n (x + 2)) cur (.n x), addS (.n (x + 3)) (.n x) (.n (x + 1))]
      (x + 4) :=
    ⟨⟨rfl, hcur.mono' (by omega), ⟨x, by omega, rfl⟩⟩,
      ⟨rfl, ⟨x, by omega, rfl⟩, ⟨x + 1, by omega, rfl⟩⟩, rfl⟩
  refine Completes.seqThen hs2 (by omega) (fun σ2 he2 hA2 => ?_)
  have hag2 : AgreeBelow (x + 2) σr σ2 := he2.agree
  have e0 : σ2 (.n (x + 2)) = σ2 cur + σ2 (.n x) :=
    hA2.atom (a := .add (.n (x + 2)) cur (.n x)) (by simp [addS])
  have e1 : σ2 (.n (x + 3)) = σ2 (.n x) + σ2 (.n (x + 1)) :=
    hA2.atom (a := .add (.n (x + 3)) (.n x) (.n (x + 1))) (by simp [addS])
  have q0 : σ2 (.n x) = kids.1 := (hag2.apply ⟨x, by omega, rfl⟩).trans hk0
  have q1 : σ2 (.n (x + 1)) = kids.2 := (hag2.apply ⟨x + 1, by omega, rfl⟩).trans hk1
  have qc : σ2 cur = σ cur := (hag2.apply (hcur.mono' (by omega))).trans (tk _ hcur)
  have qb : σ2 bit = σ bit := (hag2.apply (hbit.mono' (by omega))).trans (tk _ hbit)
  have hmul : (Atom.mul (.n (x + 2)) bit (.n (x + 3))).Holds rd σ2 :=
    isChild_check (bt := bt) (sib := sib) (by rw [q0, qc]) (by rw [q1, qc]) (by rw [qb]; exact hbv)
      e0 e1
  refine Completes.append (m := x + 4) le_rfl (by omega)
    (by simp only [mulS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil]
        exact .cons ⟨x + 2, by omega, rfl⟩ (.cons (hbit.mono' (by omega))
          (.cons ⟨x + 3, by omega, rfl⟩ (.nil _))))
    (check_complete hmul (x + 4)) (fun σ3 he3 hp3 => ?_)
  subst hp3
  refine Completes.seqThen hseq (by omega) (fun σ4 he4 hA4 => ?_)
  have hag4 : AgreeBelow (x + 4) σ3 σ4 := he4.agree
  have hagx : AgreeBelow x σ σ4 := fun j hj =>
    ((tk (.n j) ⟨j, hj, rfl⟩).symm.trans (hag2 j (by omega))).trans (hag4 j (by omega))
  have r0 : σ4 (.n x) = kids.1 := (hag4.apply ⟨x, by omega, rfl⟩).trans q0
  have r1 : σ4 (.n (x + 1)) = kids.2 := (hag4.apply ⟨x + 1, by omega, rfl⟩).trans q1
  have hp4 : PadOK σ4 pad := hp.congr hpx hagx
  have hadrc : IsCanonical128 (σ4 adr) := hac σ4 hagx hA4
  have hk := kNode_complete (C := C) (rd := rd) (pad := pad) (y := y) σ4 hp4 (by omega)
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro c (rfl | rfl | rfl | rfl | rfl)
      · exact ⟨hpp.mono' (by omega), by rw [hagx.apply hpp]; exact hppc⟩
      · exact ⟨ha0.mono' (by omega), by rw [hagx.apply ha0]; exact ha0c⟩
      · exact ⟨hadr, hadrc⟩
      · exact ⟨⟨x, by omega, rfl⟩, by rw [r0]; exact hpc.1⟩
      · exact ⟨⟨x + 1, by omega, rfl⟩, by rw [r1]; exact hpc.2⟩)
  have hk' := hk.withExt
  refine hk'.mono le_rfl le_rfl (fun σ5 h5 => ?_)
  have hag5 : AgreeBelow y σ4 σ5 := h5.2.agree
  refine ⟨fun j hj => (hagx j hj).trans (hag5 j (by omega)), ?_, ?_⟩
  · rw [← hag5 x (by omega), r0]
  · rw [← hag5 (x + 1) (by omega), r1]

/-! ## Shapes -/

/-- The values of a Keccak message, below its next base. -/
theorem kMsg_nb {pad : Nat} {cells : List KC} {len : Nat} {tailRun : Bool} {b : Nat}
    (hpb : pad + 5 ≤ b) (hc : ∀ c ∈ cells, KCb b c) (n : Nat := 1) :
    NumBelow (kMsg pad cells len tailRun none b n).2.1
        (Stmt.valsList (kMsg pad cells len tailRun none b n).1) ∧
      b ≤ (kMsg pad cells len tailRun none b n).2.1 := by
  rw [kMsg_eq]
  dsimp only
  set cs0 := cells ++ List.replicate (17 * (kBlocksOf len - 1) / 2 + 9 - cells.length) KC.zero
    with hcs0
  have hc0 : ∀ c ∈ cs0, KCb b c := by
    intro c hc'
    rcases List.mem_append.mp hc' with h | h
    · exact hc c h
    · rw [List.eq_of_mem_replicate h]; trivial
  obtain ⟨a1, a2, a3⟩ := kXorByte_seq (cs := cs0) (pos := len) (v := 1) (b := b) hc0
  set x1 := kXorByte cs0 len 1 b with hx1
  obtain ⟨b1, b2, b3⟩ := kXorByte_seq (cs := x1.2.1) (pos := 136 * kBlocksOf len - 1) (v := 0x80)
    (b := x1.2.2) a2
  set x2 := kXorByte x1.2.1 (136 * kBlocksOf len - 1) 0x80 x1.2.2 with hx2
  have hs := SeqOK.append a1 b1
  obtain ⟨n1, n2⟩ := kBlocks_nb (pad := pad) (cs := x2.2.1) (B := kBlocksOf len) (n := n)
    (tailRun := tailRun) (kBlocksOf len) 0 none x2.2.2 (by omega) (by omega) b2
    (fun s hs => by simp at hs)
  exact ⟨by rw [valsList_append]; exact (hs.numBelow.mono n2).append n1, by omega⟩

theorem kNode_numBelow {pad : Nat} {pp a0 adr k0 k1 : V} {y : Nat} (hpad : pad + 5 ≤ y)
    (h : ∀ v ∈ [pp, a0, adr, k0, k1], NBv y v) :
    NumBelow (y + 5) (Stmt.valsList (kNode pad pp a0 adr k0 k1 y).1) := by
  intro v hv
  simp only [kNode, cst, kecS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals,
    List.append_nil, List.cons_append, List.nil_append, List.mem_cons] at hv
  have hr : ∀ w ∈ runV (y + 4) 1, NBv (y + 5) w := runV_nb (by omega)
  have h0 := h pp (by simp)
  have h1 := h a0 (by simp)
  have h2 := h adr (by simp)
  have h3 := h k0 (by simp)
  have h4 := h k1 (by simp)
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | hv
  all_goals first
    | exact ⟨_, by omega, rfl⟩
    | exact h0.mono' (by omega)
    | exact h1.mono' (by omega)
    | exact h2.mono' (by omega)
    | exact h3.mono' (by omega)
    | exact h4.mono' (by omega)
    | exact hr _ hv

theorem sBe16_seq {val : Nat → V} {pos n x : Nat} (h0 : NBv x (val pos))
    (h8 : (n + 7) / 8 = 2 → NBv x (val (pos + 8))) :
    SeqOK x (sBe16 val pos n x).1 (sBe16 val pos n x).2.1 := by
  unfold sBe16
  split
  · rename_i h2
    have q := h8 h2
    exact ⟨rfl, ⟨rfl, h0.mono' (by omega), ⟨x, by omega, rfl⟩⟩, rfl,
      ⟨rfl, q.mono' (by omega), ⟨x + 2, by omega, rfl⟩⟩,
      ⟨rfl, ⟨x + 1, by omega, rfl⟩, ⟨x + 3, by omega, rfl⟩⟩, rfl⟩
  · exact ⟨rfl, ⟨rfl, h0.mono' (by omega), ⟨x, by omega, rfl⟩⟩, rfl⟩

theorem sBe16_out (val : Nat → V) (pos n x : Nat) :
    (sBe16 val pos n x).2.2 = .n ((sBe16 val pos n x).2.1 - 1) := by
  unfold sBe16; split <;> rfl

theorem sPathAddr_seq {val : Nat → V} {off z m x : Nat} (h1 : m ≠ 0 → NBv x (val (off + z + 1)))
    (h9 : 9 ≤ m → NBv x (val (off + z + 1 + 8))) :
    SeqOK x (sPathAddr val off z m x).1 (sPathAddr val off z m x).2.1 ∧
      NBv (sPathAddr val off z m x).2.1 (sPathAddr val off z m x).2.2 := by
  unfold sPathAddr
  by_cases hm0 : m = 0
  · simp only [hm0, ↓reduceIte]
    exact ⟨⟨rfl, rfl⟩, ⟨x, by omega, rfl⟩⟩
  · simp only [hm0, ↓reduceIte]
    have hs := sBe16_seq (val := val) (pos := off + z + 1) (n := m) (x := x) (h1 hm0)
      (fun h => h9 (by omega))
    have hle := hs.le
    have ho := sBe16_out val (off + z + 1) m x
    have hx : x < (sBe16 val (off + z + 1) m x).2.1 := by
      rw [sBe16_next]; split <;> omega
    refine ⟨SeqOK.append hs ⟨rfl, ⟨rfl, ?_, ⟨_, by omega, rfl⟩⟩, rfl⟩, ⟨_, by omega, rfl⟩⟩
    rw [ho]; exact ⟨_, by omega, rfl⟩

/-! ## The paths -/

theorem sPath_le (pad : Nat) (pp a0 : V) (bit val : Nat → V) (off : Nat) :
    ∀ (m z : Nat) (cur : V) (x : Nat), x ≤ (sPath pad pp a0 bit val off m z cur x).2.1
  | 0, _, _, _ => le_rfl
  | m + 1, z, cur, x => by
      rw [sPath_succ]
      dsimp only
      refine le_trans ?_ (sPath_le pad pp a0 bit val off m (z + 1)
        (.n ((sPathAddr val off z m (x + 4)).2.1 + 4)) ((sPathAddr val off z m (x + 4)).2.1 + 5))
      rw [sPathAddr_next]
      unfold pathWidth
      split_ifs <;> omega

/-- **A path completes** from level `z` (base `x`), `m` levels to the height `height`: each level's
children hinted in the order of the leaf `e`'s bit, the siblings `sib` read back, the root
canonical. -/
theorem sPath_complete {pad : Nat} {pp a0 : V} {bit val : Nat → V} {off e height : Nat}
    (hh : height ≤ 16) (he : e < 2 ^ height) {sib : Nat → E} (hsib : ∀ j, IsCanonical128 (sib j)) :
    ∀ (m z : Nat) (cur : V) (x : Nat) (σ : Val), z + m = height → pad + 5 ≤ x → NBv x pp →
      NBv x a0 → (∀ j < height, NBv x (bit (off + j))) → (∀ j < height, NBv x (val (off + j))) →
      NBv x cur → PadOK σ pad → IsCanonical128 (σ pp) → IsCanonical128 (σ a0) →
      IsCanonical128 (σ cur) →
      (∀ j < height, σ (bit (off + j)) = if e.testBit j then 1 else 0) →
      (∀ j < height, σ (val (off + j)) = eOfNat (e >>> j)) →
      Completes C rd x (sPath pad pp a0 bit val off m z cur x).2.1
        (sPath pad pp a0 bit val off m z cur x).1 σ
        (fun σ' => AgreeBelow x σ σ' ∧
          IsCanonical128 (σ' (sPath pad pp a0 bit val off m z cur x).2.2) ∧
          ∀ j, z ≤ j → j < z + m → sPathSib σ' bit off m z x j = sib j)
  | 0, z, cur, x, σ, _, _, _, _, _, _, hcur, _, _, _, hcc, _, _ =>
      ⟨σ, Ext.refl _ _ _, ⟨fun _ _ => rfl, hcc, fun j h1 h2 => by omega⟩, fun _ _ hn => hn⟩
  | m + 1, z, cur, x, σ, hm, hpx, hpp, ha0, hbn, hvn, hcur, hp, hppc, ha0c, hcc, hbit, hval => by
      rw [sPath_succ]
      set A := sPathAddr val off z m (x + 4) with hA
      obtain ⟨hseqA, hadrA⟩ := sPathAddr_seq (val := val) (off := off) (z := z) (m := m)
        (x := x + 4)
        (fun hm0 => (hvn (z + 1) (by omega)).mono' (by omega)) (fun h9 => by
          rw [show off + z + 1 + 8 = off + (z + 9) by omega]
          exact (hvn (z + 9) (by omega)).mono' (by omega))
      have hnext := sPathAddr_next val off z m x
      rw [← hA] at hseqA hadrA hnext
      have hlev := pairNode_complete (C := C) (rd := rd) "siblings" σ hp hpx hpp ha0
        (hbn z (by omega)) hcur hseqA hadrA (bt := e.testBit z) (hbit z (by omega)) (hsib z) hcc
        hppc ha0c (fun σ' hag hAt => by
          rw [hA, sPathAddr_sound (e := e) (by omega)
            (by rw [show z + 1 + m = height by omega]; exact he)
            (fun j _ hj => by rw [hag.apply (hvn j (by omega))]; exact hval j (by omega)) hAt]
          exact canon_word _ _)
      have hnb : NumBelow (A.2.1 + 5) (Stmt.valsList ([hintW "siblings" [.n x, .n (x + 1)]] ++
          isChildS cur (.n x) (.n (x + 1)) (bit (off + z)) (x + 2) ++ A.1 ++
          (kNode pad pp a0 A.2.2 (.n x) (.n (x + 1)) A.2.1).1)) := by
        have hle := hseqA.le
        simp only [valsList_append]
        refine NumBelow.append (NumBelow.append (NumBelow.append ?_ ?_) ?_) ?_
        · rw [valsList_hint]
          exact .cons ⟨x, by omega, rfl⟩ (.cons ⟨x + 1, by omega, rfl⟩ (.nil _))
        · intro v hv
          simp only [isChildS, addS, mulS, valsList_cons, valsList_nil, Stmt.vals, Atom.vals,
            List.append_nil, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
            or_false] at hv
          rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals first | exact ⟨_, by omega, rfl⟩ | exact hcur.mono' (by omega) |
            exact (hbn z (by omega)).mono' (by omega)
        · exact hseqA.numBelow.mono (by omega)
        · refine kNode_numBelow (by omega) ?_
          simp only [List.mem_cons, List.not_mem_nil, or_false]
          rintro v (rfl | rfl | rfl | rfl | rfl)
          · exact hpp.mono' (by omega)
          · exact ha0.mono' (by omega)
          · exact hadrA
          · exact ⟨x, by omega, rfl⟩
          · exact ⟨x + 1, by omega, rfl⟩
      have hle := hseqA.le
      have hx18 : x + pathWidth m = A.2.1 + 5 := by
        rw [hnext]; unfold pathWidth; split_ifs <;> omega
      refine Completes.append (m := A.2.1 + 5) (by omega)
        (sPath_le pad pp a0 bit val off m (z + 1) _ _) hnb (hlev.withAtoms (by
          simp only [atomsOnly_append, hseqA.atoms, kNode]; rfl)) (fun σ1 he1 h1 => ?_)
      obtain ⟨⟨hag1, hk0, hk1⟩, hA1⟩ := h1
      have t1 : ∀ v, NBv x v → σ1 v = σ v := fun v hv => hag1.apply hv
      obtain ⟨hib, hd⟩ := bit_facts (hbit z (by omega))
      have hib1 : IsBit (σ1 (bit (off + z))) := by rw [t1 _ (hbn z (by omega))]; exact hib
      have hp1 : PadOK σ1 pad := hp.congr hpx hag1
      have hlv := level_sound hp1 hib1
        (hA1.left.left.sub fun t ht => List.mem_append_right _ ht) hA1.right
      have hcan1 : IsCanonical128 (σ1 (.n (A.2.1 + 4))) := by rw [hlv]; exact canon_hcellFst _
      have ih := sPath_complete hh he hsib m (z + 1) (.n (A.2.1 + 4)) (A.2.1 + 5)
        σ1 (by omega) (by omega) (hpp.mono' (by omega)) (ha0.mono' (by omega))
        (fun j hj => (hbn j hj).mono' (by omega)) (fun j hj => (hvn j hj).mono' (by omega))
        ⟨A.2.1 + 4, by omega, rfl⟩ hp1 (by rw [t1 _ hpp]; exact hppc) (by rw [t1 _ ha0]; exact ha0c)
        hcan1 (fun j hj => by rw [t1 _ (hbn j hj)]; exact hbit j hj)
        (fun j hj => by rw [t1 _ (hvn j hj)]; exact hval j hj)
      refine ih.mono le_rfl le_rfl (fun σ' ⟨hag', hc', hs'⟩ => ⟨?_, hc', ?_⟩)
      · exact fun j hj => (hag1 j hj).trans (hag' j (by omega))
      · intro j hj1 hj2
        by_cases hjz : j = z
        · subst hjz
          simp only [sPathSib, ite_true]
          have hb' : σ' (bit (off + j)) = if e.testBit j then 1 else 0 := by
            rw [(hag'.apply ((hbn j (by omega)).mono' (by omega))), t1 _ (hbn j (by omega))]
            exact hbit j (by omega)
          exact siblingOf_mPair (node := σ cur) hb' (by rw [← hag' x (by omega), hk0])
            (by rw [← hag' (x + 1) (by omega), hk1])
        · simp only [sPathSib, hjz, ite_false, hx18]
          exact hs' j (by omega) (by omega)

theorem sBe16_atoms (val : Nat → V) (pos n x : Nat) : atomsOnly (sBe16 val pos n x).1 = true := by
  unfold sBe16; split <;> rfl

theorem sPathAddr_atoms (val : Nat → V) (off z m x : Nat) :
    atomsOnly (sPathAddr val off z m x).1 = true := by
  unfold sPathAddr
  split
  · rfl
  · simp only [atomsOnly_append, sBe16_atoms]; rfl

theorem sPath_atoms (pad : Nat) (pp a0 : V) (bit val : Nat → V) (off : Nat) :
    ∀ (m z : Nat) (cur : V) (x : Nat), atomsOnly (sPath pad pp a0 bit val off m z cur x).1 = true
  | 0, _, _, _ => rfl
  | m + 1, z, cur, x => by
      rw [sPath_succ]
      simp only [atomsOnly_append, sPathAddr_atoms, kNode,
        sPath_atoms pad pp a0 bit val off m (z + 1)]
      rfl

/-- **A whole path completes** to the root `pFold` of `pNodeE` from `cur`, the siblings `sib`. -/
theorem sPath_complete_val {pad : Nat} {pp a0 : V} {bit val : Nat → V} {off e height : Nat}
    (hh : height ≤ 16) (he : e < 2 ^ height) {sib : Nat → E} (hsib : ∀ j, IsCanonical128 (sib j))
    {cur : V} {x : Nat} (σ : Val) (hpx : pad + 5 ≤ x) (hpp : NBv x pp) (ha0 : NBv x a0)
    (hbn : ∀ j < height, NBv x (bit (off + j))) (hvn : ∀ j < height, NBv x (val (off + j)))
    (hcur : NBv x cur) (hp : PadOK σ pad) (hppc : IsCanonical128 (σ pp))
    (ha0c : IsCanonical128 (σ a0)) (hcc : IsCanonical128 (σ cur))
    (hbit : ∀ j < height, σ (bit (off + j)) = if e.testBit j then 1 else 0)
    (hval : ∀ j < height, σ (val (off + j)) = eOfNat (e >>> j)) :
    Completes C rd x (sPath pad pp a0 bit val off height 0 cur x).2.1
      (sPath pad pp a0 bit val off height 0 cur x).1 σ
      (fun σ' => AgreeBelow x σ σ' ∧
        σ' (sPath pad pp a0 bit val off height 0 cur x).2.2 =
          pFold (pNodeE (σ pp) (σ a0) e sib) height (σ cur) ∧
        IsCanonical128 (σ' (sPath pad pp a0 bit val off height 0 cur x).2.2)) := by
  have h := (sPath_complete (C := C) (rd := rd) hh he hsib height 0 cur x σ (by omega) hpx hpp ha0
    hbn hvn hcur hp hppc ha0c hcc hbit hval).withAtoms (sPath_atoms ..)
  refine h.mono le_rfl le_rfl (fun σ' ⟨⟨hag, hc, hs⟩, hA⟩ => ⟨hag, ?_, hc⟩)
  have t : ∀ v, NBv x v → σ' v = σ v := fun v hv => hag.apply hv
  rw [sPath_sound (hp.congr hpx hag) hh he
    (fun j hj => by rw [t _ (hbn j hj)]; exact hbit j hj)
    (fun j hj => by rw [t _ (hvn j hj)]; exact hval j hj) height 0 cur x (by omega) hA,
    ← nIter_zero, t _ hpp, t _ ha0, t _ hcur]
  refine nIter_congr_lt _ _ _ fun j _ hj => ?_
  unfold pNodeE
  rw [hs j (by omega) (by omega)]

end
end LeanVM.Guest.B1.Sig
