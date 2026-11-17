/-
  LeanVM.Guest.B1.Da.WeightsAt

  `da_weights` is complete, placed (`completeAt_flatGOutB`): its 128 expansions at fixed offsets
  of their frames, its buffer the pointers to their leaves.
-/

module

public import LeanVM.Guest.B1.Da.FlatGO
public import LeanVM.Guest.B1.Da.ExpAt
public import LeanVM.Guest.B1.Da.VecAt
public import LeanVM.Guest.B1.Da.OffAt
public import LeanVM.Guest.B1.Da.DvHonest
public import LeanVM.Guest.B1.Da.VectorMath
public import LeanVM.Guest.B1.Da.VerifyChk
public import LeanVM.Guest.Data.NameStrings

/-!
# The weights, completely

* `colShift`, `colRun`: column `h`'s expansion's shifts and run; `topRun_leaf`, `colRun_leaf`,
  `colRun_reads`: the leaves the weights read and return.
* `wsPre`, `ws_xok`: `da_weights`' body exactly, one block `wsS h` per column (kernel evaluation).
* `kidsU`: callees placed at `fps` whose words depend on their own frame pointer only;
  `atAllG_uniform` and the facts on `OutsOk`, `CallsMatch`, `RegionsOk`, `KidsGB` over them.
* `wOut`: `da_weights` returns its buffer, of pointers to word `128` of each column's run.
* `ws_completeAtB`: `da_weights` is complete, placed, within its frame, its buffer and its
  expansions' frames.
-/

namespace LeanVM.Guest.B1.Da

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (gen eOfNat)
open LeanVM.Guest.B1.Fwd LeanVM.Guest.B1.Digest
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-! ## The runs -/

theorem length_expRunVals {root : E} {F Z S : ℕ → E} {top D : ℕ} :
    (expRunVals root F Z S top D).length = 256 := by
  simp [expRunVals]

set_option maxRecDepth 8000 in
theorem length_topRun (z : E) : (topRun z).length = 256 := length_expRunVals

/-- Column `h`'s shifts: the offsets of the cell `h`. -/
def colShift (z : E) (h : ℕ) : ℕ → E := fun j => zsVal z j * ofK (wK j (128 * h))

/-- Column `h`'s expansion's run. -/
def colRun (z : E) (h : ℕ) : List E :=
  expRunVals (topLeaf z h) (factorAt (zsVal z) 6) (zsVal z) (colShift z h) 6 7

theorem length_colRun (z : E) (h : ℕ) : (colRun z h).length = 256 := length_expRunVals

theorem topRun_leaf (z : E) {h : ℕ} (hh : h < 128) :
    (topRun z).getD (128 + h) 0 = topLeaf z h := by
  have hk : 128 + h < 256 := by omega
  unfold topRun
  rw [List.getD_eq_getElem _ _ (by rw [length_expRunVals]; exact hk), expRunVals_get hk,
    ite_pos' ⟨by omega, by norm_num; omega⟩,
    show Nat.log 2 (128 + h) = 7 from log_two_pow_add (k := 7) hh,
    show (2 : ℕ) ^ 7 = 128 by norm_num, Nat.add_sub_cancel_left, topLeaf_eq z hh]

set_option maxRecDepth 8000 in
theorem colRun_leaf (z : E) (h : ℕ) {e : ℕ} (he : e < 128) :
    (colRun z h).getD (128 + e) 0 = dualAt z (128 * h + e) := by
  have hk : 128 + e < 256 := by omega
  unfold colRun
  rw [List.getD_eq_getElem _ _ (by rw [length_expRunVals]; exact hk), expRunVals_get hk,
    ite_pos' ⟨by omega, by norm_num; omega⟩,
    show Nat.log 2 (128 + e) = 7 from log_two_pow_add (k := 7) he,
    show (2 : ℕ) ^ 7 = 128 by norm_num, Nat.add_sub_cancel_left]
  exact cellLeaf_eq z he

/-- **Column `h`'s weights**, the leaves of its expansion's run. -/
theorem colRun_reads {rd : Reader} {L : Layout} (hm : MemL rd L) {c : ℕ} (z : E) (h : ℕ)
    (hq : (c, colRun z h) ∈ L) : ReadsAt rd (gen ^ (c + 128)) (colWs z h) := by
  intro e he
  have he' : e < 128 := by simpa [colWs] using he
  have := reads_of_memL hm hq (128 + e) (by rw [length_colRun]; omega)
  rw [← List.getD_eq_getElem _ 0, colRun_leaf z h he'] at this
  rw [pow_add, loadHolds_mul_gen_pow]
  simpa [colWs, he'] using this

/-! ## The body -/

/-- Column `h`'s statements: its leaf `top_leaves[h]`, the offsets' pointer `wsOff h`, the
expansion, its result at `weights[h]`. -/
def wsS (h : ℕ) : List Stmt :=
  .atom (.load (wsLeaf h) (.n 0) h) ::
    ((if h = 0 then [] else [.atom (.const (.n (4 * h + 4)) (word 128 0)),
      .atom (.mul (wsOff h) (wsOff (h - 1)) (.n (4 * h + 4)))]) ++
    [.call "da_expand__L6_L7" [wsLeaf h, .n 1, .n 2, wsOff h] [.n (4 * h + 6)],
      .atom (.load (.n (4 * h + 6)) (.n 4) h)])

/-- `da_weights`' block: its buffer, the columns, the returned pointer. -/
def wsPre : List Stmt :=
  .atom (.hint (.alloc (.n 4) 128)) ::
    ((List.range 128).flatMap wsS ++ [.atom (.copy (.n 515) (.n 4))])

/-- Column `h`'s call. -/
def wsCallS (h : ℕ) : Option V × String × List V × List V :=
  (none, "da_expand__L6_L7", [wsLeaf h, .n 1, .n 2, wsOff h], [.n (4 * h + 6)])

/-- **`da_weights`' body, exactly** (kernel evaluation). -/
noncomputable def wsXOk : Bool :=
  decide ((fn% «da_weights»).params = [.n 0, .n 1, .n 2, .n 3]) &&
  stmtsEqb (Fn.body fn% «da_weights») (wsPre ++ [.ret [.n 515]]) &&
  wsPre.all Core.Stmt.flat && wsPre.all noLoadIte && wsPre.all noDispatch &&
  decide (wsPre.filterMap Main.Stmt.addrS = []) &&
  decide (wsPre.filterMap Main.Stmt.allocSz = [(.n 4, .inl 128)]) &&
  decide (wsPre.filterMap Main.Stmt.callS = (List.range 128).map wsCallS) &&
  decide (wsPre.filterMap Stmt.loadS = (List.range 128).flatMap fun h => [(.n 0, h), (.n 4, h)])

set_option maxRecDepth 100000 in
theorem ws_xok : wsXOk = true := by decide +kernel

/-! ## The valuation -/

/-- `da_weights`' words: its arguments, its buffer `g^b`, column `h`'s leaf, `g^8`, offsets'
pointer and result `R h`. -/
def wsv (z : E) (bt bc bz bo b : ℕ) (R : ℕ → E) (i : ℕ) : E :=
  if i = 0 then gen ^ (bt + 2 ^ 7) else if i = 1 then gen ^ bc else if i = 2 then gen ^ bz
  else if i = 3 then gen ^ bo else if i = 4 ∨ i = 515 then gen ^ b
  else if i = 5 then topLeaf z 0 else if i = 6 then R 0
  else if (i - 3) % 4 = 0 then topLeaf z ((i - 3) / 4)
  else if (i - 3) % 4 = 1 then word 128 0
  else if (i - 3) % 4 = 2 then gen ^ (bo + 7 * ((i - 3) / 4))
  else R ((i - 3) / 4)

/-- `da_weights`' valuation. -/
def wsσ (z : E) (bt bc bz bo b : ℕ) (R : ℕ → E) : Val := fun v => wsv z bt bc bz bo b R v.idx

section Vals

variable {z : E} {bt bc bz bo b : ℕ} {R : ℕ → E} {h : ℕ}

theorem wsσ_n (i : ℕ) : wsσ z bt bc bz bo b R (.n i) = wsv z bt bc bz bo b R i := rfl

theorem wsv_hi {i : ℕ} (h7 : 7 ≤ i) (h515 : i ≠ 515) : wsv z bt bc bz bo b R i =
    if (i - 3) % 4 = 0 then topLeaf z ((i - 3) / 4) else if (i - 3) % 4 = 1 then word 128 0
    else if (i - 3) % 4 = 2 then gen ^ (bo + 7 * ((i - 3) / 4)) else R ((i - 3) / 4) := by
  unfold wsv
  rw [ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
    ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega)]

theorem wsσ_leaf (hh : h < 128) : wsσ z bt bc bz bo b R (wsLeaf h) = topLeaf z h := by
  unfold wsLeaf
  split_ifs with h0
  · subst h0; simp [wsσ_n, wsv]
  · rw [wsσ_n, wsv_hi (by omega) (by omega), ite_pos' (by omega)]
    congr 1; omega

theorem wsσ_off (hh : h < 128) : wsσ z bt bc bz bo b R (wsOff h) = gen ^ (bo + 7 * h) := by
  unfold wsOff
  split_ifs with h0
  · subst h0; simp [wsσ_n, wsv]
  · rw [wsσ_n, wsv_hi (by omega) (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega)]
    congr 2; omega

theorem wsσ_ret (hh : h < 128) : wsσ z bt bc bz bo b R (.n (4 * h + 6)) = R h := by
  by_cases h0 : h = 0
  · subst h0; simp [wsσ_n, wsv]
  · rw [wsσ_n, wsv_hi (by omega) (by omega), ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega)]
    congr 1; omega

theorem wsσ_c8 (h1 : 1 ≤ h) (hh : h < 128) : wsσ z bt bc bz bo b R (.n (4 * h + 4)) = gen ^ 7 := by
  rw [wsσ_n, wsv_hi (by omega) (by omega), ite_neg' (by omega), ite_pos' (by omega),
    show (128 : ℕ) = 2 ^ 7 from rfl, word_two_pow (by norm_num)]

end Vals

/-! ## Callees placed by their own frame pointer -/

/-- The callees `U a p`, `U (a+1) p'`, …, placed at the frame pointers `fps`. -/
def kidsU (U : ℕ → ℕ → Kid) : ℕ → List ℕ → List Kid
  | _, [] => []
  | a, p :: ps => U a p :: kidsU U (a + 1) ps

theorem atAllG_uniform (K : ℕ → KidG) (U : ℕ → ℕ → Kid)
    (hK : ∀ h (pre : List ℕ) p, (⟨(K h).f, (K h).taken, (K h).args pre, (K h).Lin (pre ++ [p]),
      (K h).Out (pre ++ [p])⟩ : Kid) = U h p) :
    ∀ (fps : List ℕ) (a : ℕ) (pre : List ℕ),
      atAllG pre ((List.range' a fps.length).map K) fps = kidsU U a fps
  | [], _, _ => rfl
  | p :: ps, a, pre => by
    rw [List.length_cons, List.range'_succ, List.map_cons, atAllG, kidsU, hK,
      atAllG_uniform K U hK ps (a + 1) (pre ++ [p])]

section KidsU

variable {U : ℕ → ℕ → Kid}

theorem outsOk_lengthK : ∀ {ks : List Kid} {outs : List (List E × Layout)}, OutsOk ks outs →
    outs.length = ks.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by simp [outsOk_lengthK h.2]
  | [], _ :: _, h => by simp [OutsOk] at h
  | _ :: _, [], h => by simp [OutsOk] at h

theorem outsOk_kidsU : ∀ {a : ℕ} {fps : List ℕ} {outs : List (List E × Layout)},
    OutsOk (kidsU U a fps) outs → ∀ h < fps.length, ∃ o, outs[h]? = some o ∧
      ((U (a + h) (fps.getD h 0)).taken = true → (U (a + h) (fps.getD h 0)).Out o.1 o.2) ∧
      ((U (a + h) (fps.getD h 0)).taken = true → ∀ q ∈ o.2, q ∈ takenOuts (kidsU U a fps) outs)
  | _, [], _, _, h, hh => absurd hh (by simp)
  | a, p :: ps, [], ho, _, _ => by simp [kidsU, OutsOk] at ho
  | a, p :: ps, o :: os, ho, h, hh => by
    obtain ⟨h1, h2⟩ := ho
    cases h with
    | zero =>
      refine ⟨o, rfl, by simpa using h1, fun ht q hq => ?_⟩
      simp only [Nat.add_zero, List.getD_cons_zero] at ht
      simp only [kidsU, takenOuts, List.mem_append, ht, ite_true]
      exact Or.inl hq
    | succ h =>
      obtain ⟨o', ho', hO, hT⟩ := outsOk_kidsU h2 h (by simpa using hh)
      refine ⟨o', by simpa using ho', by simpa [Nat.add_assoc, Nat.add_comm 1 h] using hO,
        fun ht q hq => ?_⟩
      simp only [kidsU, takenOuts, List.mem_append]
      exact Or.inr (hT (by simpa [Nat.add_assoc, Nat.add_comm 1 h] using ht) q hq)

theorem callsMatch_kidsU (σ : Val) (cs : ℕ → Call) : ∀ {a : ℕ} {fps : List ℕ}
    {outs : List (List E × Layout)}, outs.length = fps.length →
    (∀ h < fps.length, ∀ o, outs[h]? = some o →
      (cs (a + h)).f = (U (a + h) (fps.getD h 0)).f ∧
      (cs (a + h)).taken = (U (a + h) (fps.getD h 0)).taken ∧
      ((U (a + h) (fps.getD h 0)).taken = true →
        (cs (a + h)).args.map σ = (U (a + h) (fps.getD h 0)).args ∧ (cs (a + h)).rets.map σ = o.1)) →
    CallsMatch σ ((List.range' a fps.length).map cs) (kidsU U a fps) outs
  | _, [], [], _, _ => trivial
  | _, [], _ :: _, hl, _ => absurd hl (by simp)
  | _, _ :: _, [], hl, _ => absurd hl (by simp)
  | a, p :: ps, o :: os, hl, hc => by
    rw [List.length_cons, List.range'_succ, List.map_cons, kidsU]
    obtain ⟨c1, c2, c3⟩ := hc 0 (by simp) o rfl
    refine ⟨by simpa using c1, by simpa using c2, by simpa using c3,
      callsMatch_kidsU σ cs (by simpa using hl) fun h hh o' ho' => ?_⟩
    have := hc (h + 1) (by simpa using hh) o' (by simpa using ho')
    simpa [Nat.add_assoc, Nat.add_comm 1 h] using this

theorem regionsOk_kidsU {R : ℕ → Prop} (hR : ∀ h p, (U h p).taken = true → ∀ i,
    RegionL (U h p).Lin i → R i) :
    ∀ {a : ℕ} {fps : List ℕ} {outs : List (List E × Layout)} {D : ℕ → Prop},
      RegionsOk R D (kidsU U a fps) outs
  | _, [], _, _ => trivial
  | _, _ :: _, [], _ => trivial
  | a, p :: _, _ :: _, _ => ⟨fun ht i hi => Or.inl (hR a p ht i hi), regionsOk_kidsU hR⟩

theorem length_kidsU : ∀ (a : ℕ) (fps : List ℕ), (kidsU U a fps).length = fps.length
  | _, [] => rfl
  | a, _ :: ps => by simp [kidsU, length_kidsU (a + 1) ps]

theorem lins_kidsU : ∀ {a : ℕ} {fps : List ℕ} {q : ℕ × List E}, q ∈ Kid.lins (kidsU U a fps) →
    ∃ h p, q ∈ (U h p).Lin
  | _, [], _, hq => by simp [kidsU, Kid.lins] at hq
  | a, p :: ps, q, hq => by
    simp only [kidsU, Kid.lins, List.flatMap_cons, List.mem_append] at hq
    rcases hq with hq | hq
    · exact ⟨a, p, hq⟩
    · exact lins_kidsU (by simpa [Kid.lins] using hq)

end KidsU

variable {fs : String → ℕ} {cert : String → V → ℕ}

theorem kidsGB_range {κ B N : ℕ} (K : ℕ → KidG) (hK : ∀ h < N, (K h).taken = true → ∀ ps,
    CompleteAtFB fs cert κ (K h).f (fun p => (K h).Lin (ps ++ [p])) ((K h).args ps)
      (fun p => (K h).Out (ps ++ [p])) B) :
    ∀ n a, a + n ≤ N → KidsGB fs cert κ ((List.range' a n).map K) (List.replicate n B)
  | 0, _, _ => trivial
  | n + 1, a, han => ⟨hK a (by omega), kidsGB_range K hK n (a + 1) (by omega)⟩

theorem kidsGBound_range {B : ℕ} (K : ℕ → KidG) (hK : ∀ h, (K h).taken = true) :
    ∀ n a, kidsGBound fs ((List.range' a n).map K) (List.replicate n B) = n * B
  | 0, _ => by simp [kidsGBound]
  | n + 1, a => by
    simp only [List.range'_succ, List.map_cons, List.replicate_succ, kidsGBound, hK, ite_true,
      List.headD_cons, List.tail_cons]
    rw [kidsGBound_range K hK n (a + 1)]
    ring

/-! ## The weights -/

/-- The run's offset in `da_expand__L6_L7`'s frame. -/
noncomputable def wsC8 (cert : String → V → ℕ) : ℕ := cert "da_expand__L6_L7" (.n (expB 7 + 1))

/-- What the expansions read: `zs`, the cell factors, the offsets. -/
def wsKLin (z : E) (bz bc bo : ℕ) : Layout :=
  [(bz, zsCells z), (bc, facCells (zsVal z) 6 7), (bo, offCells (zsVal z))]

/-- **What `da_weights` reads**: `zs`, the top tree's run, the cell factors, the offsets. -/
def wsLin (z : E) (bz bt bc bo : ℕ) : Layout :=
  [(bz, zsCells z), (bt, topRun z), (bc, facCells (zsVal z) 6 7), (bo, offCells (zsVal z))]

/-- Column `h`'s expansion. -/
noncomputable def wsKid (cert : String → V → ℕ) (z : E) (bz bc bo h : ℕ) : KidG :=
  ⟨"da_expand__L6_L7", true, fun _ => [topLeaf z h, gen ^ bc, gen ^ bz, gen ^ (bo + 7 * h)],
    fun _ => wsKLin z bz bc bo,
    fun ps => expOutAt (topLeaf z h) (factorAt (zsVal z) 6) (zsVal z) (colShift z h) 6 7
      (ps.getLastD 0 + wsC8 cert)⟩

/-- Column `h`'s expansion, placed at `p`. -/
noncomputable def wsU (cert : String → V → ℕ) (z : E) (bz bc bo : ℕ) (h p : ℕ) : Kid :=
  ⟨"da_expand__L6_L7", true, [topLeaf z h, gen ^ bc, gen ^ bz, gen ^ (bo + 7 * h)],
    wsKLin z bz bc bo,
    expOutAt (topLeaf z h) (factorAt (zsVal z) 6) (zsVal z) (colShift z h) 6 7 (p + wsC8 cert)⟩

/-- The buffer: column `h`'s pointer to word `128` of its run in the frame at `fps[h]`. -/
noncomputable def wsCells (cert : String → V → ℕ) (fps : List ℕ) : List E :=
  (List.range 128).map fun h => gen ^ (fps.getD h 0 + wsC8 cert + 128)

/-- **`da_weights` returns its buffer** `g^b`, word `h` a pointer to word `128` of column `h`'s
run, at `q h`. -/
def wOut (z : E) : List E → Layout → Prop := fun rets Lo =>
  ∃ (b : ℕ) (q : ℕ → ℕ), rets = [gen ^ b] ∧
    (b, (List.range 128).map fun h => gen ^ (q h + 128)) ∈ Lo ∧ ∀ h < 128, (q h, colRun z h) ∈ Lo

theorem ws_atAllG (z : E) (bz bc bo : ℕ) {fps : List ℕ} (hl : fps.length = 128) :
    atAllG [] ((List.range' 0 128).map (wsKid cert z bz bc bo)) fps = kidsU (wsU cert z bz bc bo) 0 fps := by
  rw [← hl]
  exact atAllG_uniform _ _ (fun h pre p => by simp [wsKid, wsU]) fps 0 []

theorem ws_kLin_sub {z : E} {bz bt bc bo : ℕ} {q : ℕ × List E} (hq : q ∈ wsKLin z bz bc bo) :
    q ∈ wsLin z bz bt bc bo := by
  simp only [wsKLin, wsLin, List.mem_cons, List.not_mem_nil, or_false] at hq ⊢
  tauto

set_option maxRecDepth 20000 in
/-- **`da_weights` is complete, placed, within its frame, its buffer and its expansions'
frames.** -/
theorem ws_completeAtB (hrf : Lift.RunsFit fs cert) (z : E) (bz bt bc bo : ℕ) :
    CompleteAtB fs cert 16 "da_weights" (wsLin z bz bt bc bo)
      [gen ^ (bt + 2 ^ 7), gen ^ bc, gen ^ bz, gen ^ bo] (wOut z)
      (fs "da_weights" + 128 + 128 * fs "da_expand__L6_L7") := by
  have hx := ws_xok
  unfold wsXOk at hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hpar, hbody⟩, hflat⟩, hnli⟩, hnd⟩, haddr⟩, halloc⟩, hcalls⟩, hloads⟩ := hx
  have hb : (fn% «da_weights»).body = wsPre ++ [.ret [.n 515]] := stmtsEqb_sound hbody
  have hLz : ∀ {rd : Reader}, MemL rd (wsKLin z bz bc bo) →
      ∀ j < 14, LoadHolds rd (gen ^ bz) j (zsVal z j) := fun hm j hj => by
    have := reads_of_memL hm List.mem_cons_self j (by simp [zsCells]; exact hj)
    rwa [zsCells_get hj] at this
  have e := completeAt_flatGOutB (fs := fs) (cert := cert) find_da_weights
    (by rw [Program.loop_of_find? find_da_weights]; decide +kernel) 16 (wsLin z bz bt bc bo)
    [gen ^ (bt + 2 ^ 7), gen ^ bc, gen ^ bz, gen ^ bo]
    (fun fp _ => [gen ^ (fp + fs "da_weights")]) (wOut z) hb hflat haddr hnli [128]
    (fun _ fps => [wsCells cert fps]) (fun _ _ => .cons (by simp [wsCells]) .nil)
    (fun _ => (List.range' 0 128).map (wsKid cert z bz bc bo))
    (List.replicate 128 (fs "da_expand__L6_L7")) (128 * fs "da_expand__L6_L7")
    (fun _ => kidsGB_range (N := 128) _ (fun h hh _ ps => ?_) 128 0 le_rfl)
    (fun _ => le_of_eq (kidsGBound_range _ (fun _ => rfl) 128 0)) (fun fp fps outs hl ho => ?_)
    (fun fp fps outs hl _ ho rd _ hB hLin _ => ?_)
  · simpa using e
  · -- an expansion
    have := expCell_completeAtFB fs cert hrf (Lin := wsKLin z bz bc bo) (root := topLeaf z h)
      (cf := bc) (cz := bz) (cs := bo + 7 * h) (F := factorAt (zsVal z) 6) (Z := zsVal z)
      (S := colShift z h) (fun rd hm n h1 h2 => ?_)
      (fun rd hm d hd => hLz hm _ (by omega)) (fun rd hm d hd => ?_)
      (fun n h1 h2 => regionL_of_mem (List.mem_cons_of_mem _ List.mem_cons_self)
        (by simp [facCells]; omega))
      (fun d hd => regionL_of_mem List.mem_cons_self (by simp [zsCells]; omega))
      (fun d hd => by
        have := regionL_of_mem (L := wsKLin z bz bc bo) (k := 7 * h + (6 - d))
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
          (by simp [offCells]; omega)
        rwa [← Nat.add_assoc] at this)
    · have hl : ∀ p, (ps ++ [p]).getLastD 0 = p := fun p => by simp [List.getLastD_eq_getLast?]
      simpa [wsKid, wsC8, hl] using this
    · have := reads_of_memL hm (List.mem_cons_of_mem _ List.mem_cons_self) n
        (by simp [facCells]; omega)
      rwa [facCells_get h1 h2 (by norm_num)] at this
    · have := reads_of_memL hm (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
        (7 * h + (6 - d)) (by simp [offCells]; omega)
      rw [offCells_get (by omega), show (7 * h + (6 - d)) % 7 = 6 - d by omega,
        show (7 * h + (6 - d)) / 7 = h by omega] at this
      rw [pow_add, loadHolds_mul_gen_pow]
      exact this
  · -- the result
    have hl' : fps.length = 128 := by simpa using hl
    rw [ws_atAllG z bz bc bo hl'] at ho ⊢
    refine ⟨fp + fs "da_weights", fun h => fps.getD h 0 + wsC8 cert, rfl,
      List.mem_append_left _ (by simp [bufL, bases, wsCells]), fun h hh => ?_⟩
    obtain ⟨o, -, hO, hT⟩ := outsOk_kidsU ho h (by omega)
    simp only [wsU, Nat.zero_add] at hO hT
    exact List.mem_append_right _ (hT trivial _ (hO trivial).2)
  · -- the valuation
    have hl' : fps.length = 128 := by simpa using hl
    rw [ws_atAllG z bz bc bo hl'] at ho ⊢
    set R : ℕ → E := fun h => gen ^ (fps.getD h 0 + wsC8 cert + 128) with hR
    set σ := wsσ z bt bc bz bo (fp + fs "da_weights") R with hσdef
    have hbuf : ReadsAt rd (gen ^ (fp + fs "da_weights")) (wsCells cert fps) :=
      reads_of_memL hB (by simp [bufL, bases])
    have s0 : σ (.n 0) = gen ^ (bt + 2 ^ 7) := by simp [hσdef, wsσ_n, wsv]
    have s4 : σ (.n 4) = gen ^ (fp + fs "da_weights") := by simp [hσdef, wsσ_n, wsv]
    have hall : ∀ s ∈ wsPre, SHolds (fun _ _ _ => True) rd σ s := by
      intro s hs
      simp only [wsPre, List.mem_cons, List.mem_append, List.mem_flatMap, List.mem_range,
        List.not_mem_nil, or_false] at hs
      rcases hs with rfl | ⟨h, hh, hs⟩ | rfl
      · trivial
      · simp only [wsS, List.mem_cons, List.mem_append] at hs
        rcases hs with rfl | hs
        · show LoadHolds rd (σ (.n 0)) h (σ (wsLeaf h))
          rw [s0, hσdef, wsσ_leaf hh, pow_add, loadHolds_mul_gen_pow,
            show (2 : ℕ) ^ 7 = 128 by norm_num]
          exact loadHolds_of_reads (reads_of_memL hLin (List.mem_cons_of_mem _ List.mem_cons_self))
            (by rw [length_topRun]; omega) (topRun_leaf z hh)
        rcases hs with hs | hs
        · split_ifs at hs with h0
          · simp at hs
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl
          · show σ (.n (4 * h + 4)) = word 128 0
            rw [hσdef, wsσ_c8 (by omega) hh, show (128 : ℕ) = 2 ^ 7 from rfl,
              word_two_pow (by norm_num)]
          · show σ (wsOff h) = σ (wsOff (h - 1)) * σ (.n (4 * h + 4))
            rw [hσdef, wsσ_off hh, wsσ_off (by omega), wsσ_c8 (by omega) hh, ← pow_add]
            congr 1; omega
        · simp only [List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl
          · trivial
          · show LoadHolds rd (σ (.n 4)) h (σ (.n (4 * h + 6)))
            rw [s4, hσdef, wsσ_ret hh]
            exact loadHolds_of_reads hbuf (by simp [wsCells]; omega) (by simp [wsCells, hh, hR])
      · show σ (.n 515) = σ (.n 4)
        simp [hσdef, wsσ_n, wsv]
    have hcs : wsPre.filterMap (Stmt.callSF σ) = (List.range 128).map wsCallS := by
      rw [← hcalls]
      refine List.filterMap_congr fun s hs => ?_
      have := List.all_eq_true.mp hnd s hs
      cases s with
      | dispatch => simp [noDispatch] at this
      | _ => rfl
    refine ⟨fun q hq => ?_, regionsOk_kidsU (fun h p _ i hi => Or.inl ?_), σ, ?_, fun s hs => ?_,
      ?_, ?_, ?_, ?_, ?_⟩
    · obtain ⟨h, p, hq'⟩ := lins_kidsU hq
      exact hLin q (ws_kLin_sub (by simpa [wsU] using hq'))
    · obtain ⟨q, hq, h1, h2⟩ := hi
      exact ⟨q, ws_kLin_sub (by simpa [wsU] using hq), h1, h2⟩
    · rw [hpar]; simp [hσdef, wsσ_n, wsv]
    · have := List.all_eq_true.mp hnd s hs
      cases s with
      | dispatch => simp [noDispatch] at this
      | _ => trivial
    · rw [hb]
      exact holdsList_straight _ _ _ _ hall (by simp [hσdef, wsσ_n, wsv])
    · rw [halloc]; rfl
    · rw [halloc]
      simp [bases, s4, gen_pow_eq_ofK]
    · rw [hcs, List.map_map, List.range_eq_range', ← hl']
      refine callsMatch_kidsU σ (fun h => Main.mkCall σ (wsCallS h))
        (by rw [outsOk_lengthK ho, length_kidsU]) fun h hh o ho' => ?_
      obtain ⟨o', ho'', hO, -⟩ := outsOk_kidsU ho h hh
      rw [ho'] at ho''
      cases ho''
      simp only [Nat.zero_add, wsU, wsCallS, Main.mkCall] at hO ⊢
      obtain ⟨hr, -⟩ := hO trivial
      refine ⟨trivial, trivial, fun _ => ⟨?_, ?_⟩⟩
      · simp only [List.map_cons, List.map_nil]
        rw [hσdef, wsσ_leaf (by omega), wsσ_off (by omega)]
        simp [wsσ_n, wsv]
      · rw [hr]
        simp only [List.map_cons, List.map_nil]
        rw [hσdef, wsσ_ret (by omega)]
        simp [hR]
    · rw [hloads]
      intro q hq
      simp only [List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil,
        or_false] at hq
      obtain ⟨h, hh, rfl | rfl⟩ := hq
      · refine ⟨bt + 2 ^ 7 + h, by rw [s0]; exact limb0_gen_pow_mul _ _, Or.inl ?_⟩
        have := regionL_of_mem (L := wsLin z bz bt bc bo) (k := 2 ^ 7 + h)
          (List.mem_cons_of_mem _ List.mem_cons_self) (by rw [length_topRun]; omega)
        rwa [← Nat.add_assoc] at this
      · exact ⟨fp + fs "da_weights" + h, by rw [s4]; exact limb0_gen_pow_mul _ _,
          Or.inr (Or.inl (regionL_of_mem (L := bufL (fp + fs "da_weights") [128] [wsCells cert fps])
            (xs := wsCells cert fps) (by simp [bufL, bases]) (by simp [wsCells]; omega)))⟩


end
end LeanVM.Guest.B1.Da
