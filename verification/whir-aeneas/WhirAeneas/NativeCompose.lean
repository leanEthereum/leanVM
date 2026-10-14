import WhirAeneas.NativeReads
import WhirAeneas.Authenticated

/-! The composed theorem for the generated native opening verifier (`OpeningVerifier` for
`VerifierState` over the BLAKE2s duplex, extracted with the replay), without assuming its
transcript reads: `NativeReads.native_transcript` derives `Transcript` from the duplex,
proof-of-work hash and Merkle hash content contracts, so `verify_eq` holds when the proof answers
the script (`NativeAnswers`). Under injective leaf and pair hashes, openings against committed
trees authenticate the script's rows: `AuthenticatedRows` holds for the script's opening with the
committed tables, the per-level accepting hints read off the same `NativeAnswers`. The equality
check's `EnsureModel` holds for any injective element interpretation (`ensure_native`), and the
committed tables have the shapes `nativeVerify_refines` needs, so `verify_refines_native` concludes
the model's `Protocol.verify` from the source's acceptance. -/
namespace WhirAeneas.Native
open Aeneas Aeneas.Std Whir Whir.Concrete Whir.WHIRNativeArithmetic WhirAeneas.Merkle
  WhirAeneas.MerkleNative WhirAeneas.Replay WhirAeneas.Fold WhirAeneas.Query WhirAeneas.NativeReads

section Ensure

/-- The limb interpretation of `F192` as the model's extension element. -/
def limbs (x : NativeReads.F192) : Concrete.E := ⟨x.c0.bv.toNat.toUInt64, x.c1.bv.toNat.toUInt64, x.c2.bv.toNat.toUInt64⟩

theorem limb_inj (x y : U64) (h : x.bv.toNat.toUInt64 = y.bv.toNat.toUInt64) : x = y := by
  have hx := x.bv.isLt
  have hy := y.bv.isLt
  have h' := congrArg UInt64.toNat h
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat'] at h'
  rw [Nat.mod_eq_of_lt (by simpa using hx), Nat.mod_eq_of_lt (by simpa using hy)] at h'
  cases x; cases y
  simp only [UScalar.mk.injEq]
  exact BitVec.eq_of_toNat_eq h'

theorem limbs_injective : Function.Injective limbs := by
  intro a b h
  simp only [limbs, Concrete.E.mk.injEq] at h
  obtain ⟨h0, h1, h2⟩ := h
  cases a; cases b
  simp only [ReplaySource.primitives.field.gf2_64x3.F192.mk.injEq]
  exact ⟨limb_inj _ _ h0, limb_inj _ _ h1, limb_inj _ _ h2⟩

/-- The generated `ensure_eq` compares the three limbs, so it decides the interpreted equality
for an injective interpretation. -/
theorem ensure_native (encode : NativeReads.F192 → Concrete.E) (henc : Function.Injective encode) :
    EnsureModel nativeInst encode := by
  intro Er T2 f v a b c ⟨e, he⟩
  have hab : encode a = encode b ↔ a = b := ⟨fun h => henc h, fun h => h ▸ rfl⟩
  rw [hab]
  by_cases h : a = b
  · subst h
    refine ⟨.Ok (), v, ?_, by simp⟩
    simp [ReplaySource.fiat_shamir.verifier.VerifierState.Insts.Fiat_shamirArithVerifierF192.ensure_eq,
      ReplaySource.primitives.field.gf2_64x3.F192.Insts.CoreCmpPartialEqF192.eq]
  · refine ⟨.Err e, v, ?_, by simp [h]⟩
    have hne : ¬ (a.c0 = b.c0 ∧ a.c1 = b.c1 ∧ a.c2 = b.c2) := by
      rintro ⟨h0, h1, h2⟩; cases a; cases b; simp_all
    simp only [ReplaySource.fiat_shamir.verifier.VerifierState.Insts.Fiat_shamirArithVerifierF192.ensure_eq,
      ReplaySource.primitives.field.gf2_64x3.F192.Insts.CoreCmpPartialEqF192.eq]
    by_cases h0 : a.c0 = b.c0 <;> by_cases h1 : a.c1 = b.c1 <;> by_cases h2 : a.c2 = b.c2 <;>
      simp_all

/-- The native element clone is the identity. -/
theorem clone_native :
    ∀ x, nativeInst.fiat_shamirarithVerifierInst.ArithInst.coremarkerCopyInst.cloneInst.clone x = .ok x :=
  fun _ => rfl

end Ensure

section Loop
variable (encode : NativeReads.F192 → Concrete.E)
  (const : ReplaySource.primitives.field.gf2_64x3.F192 → Concrete.E)
  (encodeK : U64 → Concrete.K) (ofLimbs : Concrete.K → Concrete.K → Concrete.K → Concrete.E)
  (index : Usize → Nat)

/-- The composed theorem for the generated native opening verifier: `verify_eq` with every read
derived from the extracted transcript, the duplex, proof-of-work and Merkle hash contracts, and
what the proof holds (`NativeAnswers`), instead of assumed; the equality check is the generated
`ensure_eq` for an injective `encode` and the element clone is the identity by definition. -/
theorem verify_eq_native {T1 : Type} (hw : System.Platform.numBits = 64)
    (h : ArithModel nativeInst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (hr : RowModel nativeInst encode encodeK ofLimbs index) (hn : NormalizerModel const)
    {out : List DOp → Nat → List U8} {R : ReplaySource.fiat_shamir.duplex.Blake2sDuplex → List DOp → Prop}
    (hD : Duplex out R) {H : List U8 → Digest} (hH : PowHash H)
    {leaf : List U64 → Digest} {node : Digest → Digest → Digest} (hR : RowHash leaf) (hP : PairHash node)
    (henc : Function.Injective encode)
    (W : ReplaySource.whir.verify.WeightAt T1 NativeReads.F192 VS Digest ReplaySource.primitives.field.gf2_64.F64 Usize)
    (weight_at : T1) (callerAt : Array Concrete.E → Concrete.E) (hcall : CallerModel W weight_at encode callerAt)
    (config : ReplaySource.whir.config.Config) (c : Protocol.Config) (log_n : Usize) (hcfg : ConfigRel config c log_n)
    (s : Script NativeReads.F192 Usize Digest ReplaySource.primitives.field.gf2_64.F64) (n_lanes : Usize)
    (hch : (s.chal encode).valid c = true) (hS : ScriptShape index c s n_lanes.val) (hgs : GrindShape config s)
    (target : NativeReads.F192) (root : Digest) (v : VS) (rest : List NEvent)
    (hroot : ∀ (hl : 0 < s.levels.length), (s.levels[0]'hl).root = root)
    (hv : NativeAnswers out R H leaf node v (s.tape ++ rest)) :
    ∃ r v', ReplaySource.whir.verify.verify nativeInst W v config log_n n_lanes target root weight_at = .ok (r, v') ∧
      (r = .Ok () ↔ nativeVerify c (s.chal encode) n_lanes.val (encode target) callerAt
        (s.prf encode encodeK ofLimbs) = .ok ()) :=
  verify_eq nativeInst encode const encodeK ofLimbs index _ hw h hr hn
    (native_transcript hw hD hH hR hP encode) clone_native (ensure_native encode henc) W weight_at callerAt hcall
    config c log_n hcfg s n_lanes hch hS hgs target root v rest hroot hv

end Loop

/-! ## Authentication against committed trees -/

theorem remaining_zero (c : Protocol.Config) (h : 0 < c.folds.size) :
    CausalGame.remaining c 0 = c.logN - c.folds[0]! := by
  unfold CausalGame.remaining
  rw [List.take_add_one, List.take_zero, List.nil_append, Array.getElem?_toList,
    Array.getElem?_eq_getElem h, getElem!_pos c.folds 0 h]
  simp

theorem remaining_succ (c : Protocol.Config) (i : Nat) (h : i + 1 < c.folds.size) :
    CausalGame.remaining c (i + 1) = CausalGame.remaining c i - c.folds[i + 1]! := by
  unfold CausalGame.remaining
  rw [List.take_add_one (i := i + 1), List.sum_append, Array.getElem?_toList,
    Array.getElem?_eq_getElem h, getElem!_pos c.folds (i + 1) h]
  simp [Nat.sub_sub]

section Auth
variable {E : Type} (encode : E → Concrete.E) (encodeK : U64 → Concrete.K)
  (ofLimbs : Concrete.K → Concrete.K → Concrete.K → Concrete.E)

/-- A committed oracle table: `2 ^ depth` rows, row `k` the model's reading of `C k`. -/
def tableOf (base : Bool) (depth : Nat) (C : Nat → List U64) : Protocol.Oracle :=
  ((List.range (2 ^ depth)).map fun k => encRow encodeK ofLimbs base (C k)).toArray

/-- Level `j`'s recorded depth. -/
def depthOf (s : Script E Usize Digest U64) (j : Nat) : Nat := (s.levels[j]?.map SLevel.depth).getD 0

/-- Under injective leaf and pair hashes: if every level's rows are opened by a hint against
the root of that level's committed tree `T j` over rows `C j`, the script's opening with the
committed tables satisfies `AuthenticatedRows` against the first table. -/
theorem authenticated_native (c : Protocol.Config) (s : Script E Usize Digest U64) (lanes : Nat)
    (hS : ScriptShape (fun q : Usize => q.val) c s lanes)
    (leaf : List U64 → Digest) (node : Digest → Digest → Digest)
    (hleaf : ∀ a b, leaf a = leaf b → a = b) (hnode : ∀ a b c d, node a b = node c d → a = c ∧ b = d)
    (C : Nat → Nat → List U64) (T : Nat → Nat → Nat → Digest)
    (hT0 : ∀ j (hj : j < s.levels.length) i, T j 0 i =
      leaf (List.replicate (s.levels[j].leafWords - s.levels[j].rowWords)
        ReplaySource.primitives.field.gf2_64.F64.ZERO ++ C j i))
    (hT : ∀ j l i, T j (l + 1) i = node (T j l (2 * i)) (T j l (2 * i + 1)))
    (hroots : ∀ j (hj : j < s.levels.length), s.levels[j].root = T j s.levels[j].depth 0)
    (hopen : ∀ j (hj : j < s.levels.length), ∃ hint, HintOpens leaf node s.levels[j].root s.levels[j].depth
      (s.levels[j].queries.map (·.val)) s.levels[j].rowWords s.levels[j].leafWords s.levels[j].rows hint) :
    AuthenticatedRows c (s.chal encode) (withOracles (s.prf encode encodeK ofLimbs)
      fun j => tableOf encodeK ofLimbs (j == 0) (depthOf s j) (C j))
      (tableOf encodeK ofLimbs true (depthOf s 0) (C 0)) := by
  have key := authenticated_withOracles encode encodeK ofLimbs (fun q : Usize => q.val) c s lanes hS
    (fun j => tableOf encodeK ofLimbs (j == 0) (depthOf s j) (C j)) ?_
  · simpa using key
  intro j hj i hi
  obtain ⟨hint, hh⟩ := hopen j hj
  rw [hroots j hj] at hh
  obtain ⟨hws, hin⟩ := hint_binding leaf node hleaf hnode _ _ _ _ _ hint (C j) (T j) (hT0 j hj) (hT j) hh
  have hiq : i < s.levels[j].queries.length := by rw [← hS.rows j hj]; exact hi
  have hrow : s.levels[j].rows[i] = C j (s.levels[j].queries[i]).val := by
    have := List.getElem_of_eq hws (i := i) hi
    simpa using this
  have hlt : (s.levels[j].queries[i]).val < 2 ^ depthOf s j := by
    rw [depthOf, List.getElem?_eq_getElem hj]
    exact hin _ (List.mem_map_of_mem (List.getElem_mem hiq))
  rw [hrow]
  simp only [tableOf]
  rw [getElem!_pos _ _ (by simpa using hlt)]
  simp

/-! ### Shapes of the committed tables -/

theorem encRow_true_size (w : List U64) : (encRow encodeK ofLimbs true w).size = w.length := by
  simp [encRow]

theorem encRow_false_size (w : List U64) : (encRow encodeK ofLimbs false w).size = w.length / 3 := by
  simp [encRow, eRow]

theorem tableOf_valid (base : Bool) (d width : Nat) (C : Nat → List U64)
    (hw : ∀ k < 2 ^ d, (encRow encodeK ofLimbs base (C k)).size = width) :
    Protocol.oracleValid (tableOf encodeK ofLimbs base d C) (2 ^ d) width = true := by
  have hsz : (tableOf encodeK ofLimbs base d C).size = 2 ^ d := by simp [tableOf]
  unfold Protocol.oracleValid
  rw [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true_iff_forall_mem]
  refine ⟨hsz, ?_⟩
  intro row hrow
  simp only [tableOf, List.mem_toArray, List.mem_map, List.mem_range] at hrow
  obtain ⟨k, hk, rfl⟩ := hrow
  simpa using hw k hk

/-- The first committed table has the shape `nativeVerify_refines` asks of the root oracle when
each committed level-0 row has the level's row width. -/
theorem root_shape (c : Protocol.Config) (s : Script E Usize Digest U64) (lanes : Nat)
    (hS : ScriptShape (fun q : Usize => q.val) c s lanes) (hc : c.valid = true) (C : Nat → Nat → List U64)
    (hC : ∀ j (hj : j < s.levels.length) k, k < 2 ^ s.levels[j].depth → (C j k).length = s.levels[j].rowWords) :
    Protocol.oracleValid (tableOf encodeK ofLimbs true (depthOf s 0) (C 0))
      (2 ^ (c.logN - c.folds[0]! + c.rates[0]!)) lanes = true := by
  have hf := (WHIRNativeGuards.config_header c hc).1
  have h0 : 0 < s.levels.length := by rw [hS.len]; omega
  have hd : depthOf s 0 = c.logN - c.folds[0]! + c.rates[0]! := by
    rw [depthOf, List.getElem?_eq_getElem h0]
    simp only [Option.map_some, Option.getD_some]
    rw [hS.depth 0 h0, remaining_zero c (by omega)]
  rw [← hd]
  apply tableOf_valid
  intro k hk
  rw [encRow_true_size, hC 0 h0 k (by rwa [depthOf, List.getElem?_eq_getElem h0] at hk),
    (hS.baseWords h0).1]

/-- The committed tables in place of the presence markers have the shapes `RootShapes` asks of
the next oracles when each committed row has its level's row width. -/
theorem root_shapes (c : Protocol.Config) (s : Script E Usize Digest U64) (lanes : Nat)
    (hS : ScriptShape (fun q : Usize => q.val) c s lanes) (C : Nat → Nat → List U64)
    (hC : ∀ j (hj : j < s.levels.length) k, k < 2 ^ s.levels[j].depth → (C j k).length = s.levels[j].rowWords)
    (P : Protocol.Opening) :
    RootShapes c (withOracles P fun j => tableOf encodeK ofLimbs (j == 0) (depthOf s j) (C j)) := by
  intro i hi hi1 next hnext
  rw [withOracles_level] at hnext
  simp only [Option.map_eq_some_iff] at hnext
  obtain ⟨_, _, rfl⟩ := hnext
  have hl : i + 1 < s.levels.length := by rw [hS.len]; exact hi1
  have hd : depthOf s (i + 1) =
      CausalGame.remaining c i - c.folds[i + 1]! + c.rates[i + 1]! := by
    rw [depthOf, List.getElem?_eq_getElem hl]
    simp only [Option.map_some, Option.getD_some]
    rw [hS.depth (i + 1) hl, remaining_succ c i hi1]
  simp only [show (i + 1 == 0) = false from rfl]
  rw [← hd]
  apply tableOf_valid
  intro k hk
  rw [encRow_false_size,
    hC (i + 1) hl k (by rwa [depthOf, List.getElem?_eq_getElem hl] at hk),
    (hS.extWords (i + 1) hl (by omega)).1]
  omega

end Auth

/-- Every rows event a proof answers is opened by its hint. -/
theorem answers_rows {out : List DOp → Nat → List U8} {H : List U8 → Digest} {leaf : List U64 → Digest}
    {node : Digest → Digest → Digest} :
    ∀ (evs : List NEvent) (h : List DOp) (n hs : List U8), Answers out H leaf node h n hs evs →
      ∀ root depth qs rw lw ws, Event.rows root depth qs rw lw ws ∈ evs →
        ∃ hint, HintOpens leaf node root depth (qs.map (·.val)) rw lw ws hint := by
  intro evs
  induction evs with
  | nil => intro _ _ _ _ _ _ _ _ _ _ hm; simp at hm
  | cons e evs ih =>
    intro h n hs hA root depth qs rw lw ws hm
    rcases List.mem_cons.mp hm with he | htl
    · subst he
      simp only [Answers] at hA
      obtain ⟨_, hint, _, _, _, hh, _⟩ := hA
      exact ⟨hint, hh⟩
    · cases e with
      | sample _ => simp only [Answers] at hA; exact ih _ _ _ hA.2.2 _ _ _ _ _ _ htl
      | sampleVec _ => simp only [Answers] at hA; exact ih _ _ _ hA.2.2 _ _ _ _ _ _ htl
      | scalar _ => simp only [Answers] at hA; exact ih _ _ _ hA.2.2 _ _ _ _ _ _ htl
      | scalars _ => simp only [Answers] at hA; exact ih _ _ _ hA.2.2 _ _ _ _ _ _ htl
      | poly _ _ => simp only [Answers] at hA; exact ih _ _ _ hA.2.2 _ _ _ _ _ _ htl
      | root _ => simp only [Answers] at hA; exact ih _ _ _ hA.2.2 _ _ _ _ _ _ htl
      | grind b =>
        simp only [Answers] at hA
        by_cases hb : b = 0
        · exact ih _ _ _ (hA.2.1 hb) _ _ _ _ _ _ htl
        · exact ih _ _ _ (hA.2.2 hb).2.2.2 _ _ _ _ _ _ htl
      | queries _ _ => simp only [Answers] at hA; exact ih _ _ _ hA.2.2.2.2 _ _ _ _ _ _ htl
      | rows _ _ _ _ _ _ =>
        simp only [Answers] at hA
        obtain ⟨_, _, _, _, _, _, hrest⟩ := hA
        exact ih _ _ _ hrest _ _ _ _ _ _ htl

/-- The per-level accepting hints of `authenticated_native`, read off the proof that answers the
script: each level's rows event is in the script's reads, so its hint opens its rows. -/
theorem level_hints {out : List DOp → Nat → List U8} {R : ReplaySource.fiat_shamir.duplex.Blake2sDuplex → List DOp → Prop}
    {H : List U8 → Digest} {leaf : List U64 → Digest} {node : Digest → Digest → Digest}
    (s : Script NativeReads.F192 Usize Digest U64) (v : VS) (rest : List NEvent)
    (hv : NativeAnswers out R H leaf node v (s.tape ++ rest)) :
    ∀ j (hj : j < s.levels.length), ∃ hint, HintOpens leaf node s.levels[j].root s.levels[j].depth
      (s.levels[j].queries.map (·.val)) s.levels[j].rowWords s.levels[j].leafWords s.levels[j].rows hint := by
  intro j hj
  obtain ⟨_, h, _, hA⟩ := hv
  apply answers_rows _ h _ _ hA
  simp only [Script.tape, List.mem_append, List.mem_cons, List.mem_flatMap]
  refine Or.inl (Or.inr (Or.inl ⟨s.levels[j], List.getElem_mem hj, ?_⟩))
  simp [levelTape, batchTape]

/-- `nativeVerify` accepts only lane counts in `1 .. 2 ^ folds[0]`. -/
theorem nativeVerify_lanes (c : Protocol.Config) (ch : Protocol.Challenges) (lanes : Nat) (x : Concrete.E)
    (callerAt : Array Concrete.E → Concrete.E) (P : Protocol.Opening)
    (h : nativeVerify c ch lanes x callerAt P = .ok ()) : 0 < lanes ∧ lanes ≤ 2 ^ c.folds[0]! := by
  unfold nativeVerify at h
  by_cases hg : (!ch.valid c || lanes == 0 || decide (lanes > 2 ^ c.folds[0]!)) = true
  · simp only [hg, ↓reduceIte] at h; cases h
  · simp only [Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, beq_iff_eq, decide_eq_true_eq,
      not_or] at hg
    omega

section Refines
variable (encode : NativeReads.F192 → Concrete.E)
  (const : ReplaySource.primitives.field.gf2_64x3.F192 → Concrete.E)
  (encodeK : U64 → Concrete.K) (ofLimbs : Concrete.K → Concrete.K → Concrete.K → Concrete.E)

/-- The model's verifier accepts what the generated native verifier accepts. Under the premises
of `verify_eq_native` (with query positions read as their values), injective leaf and pair hashes,
committed trees `T j` over rows `C j` of the levels' row widths whose roots are the script's roots,
and a caller weight `b` of the cube's size, zero past the lanes, whose multilinear extension the
caller evaluates: when the generated `verify` returns `Ok`, `Protocol.verify` accepts the script's
challenges and opening with the committed tables against the first table. -/
theorem verify_refines_native {T1 : Type} (hw : System.Platform.numBits = 64)
    (h : ArithModel nativeInst.fiat_shamirarithVerifierInst.ArithInst encode const)
    (hr : RowModel nativeInst encode encodeK ofLimbs (fun q : Usize => q.val)) (hn : NormalizerModel const)
    {out : List DOp → Nat → List U8} {R : ReplaySource.fiat_shamir.duplex.Blake2sDuplex → List DOp → Prop}
    (hD : Duplex out R) {H : List U8 → Digest} (hH : PowHash H)
    {leaf : List U64 → Digest} {node : Digest → Digest → Digest} (hR : RowHash leaf) (hP : PairHash node)
    (hleaf : ∀ a b, leaf a = leaf b → a = b) (hnode : ∀ a b c d, node a b = node c d → a = c ∧ b = d)
    (henc : Function.Injective encode)
    (W : ReplaySource.whir.verify.WeightAt T1 NativeReads.F192 VS Digest ReplaySource.primitives.field.gf2_64.F64 Usize)
    (weight_at : T1) (callerAt : Array Concrete.E → Concrete.E) (hcall : CallerModel W weight_at encode callerAt)
    (config : ReplaySource.whir.config.Config) (c : Protocol.Config) (log_n : Usize) (hcfg : ConfigRel config c log_n)
    (s : Script NativeReads.F192 Usize Digest ReplaySource.primitives.field.gf2_64.F64) (n_lanes : Usize)
    (hch : (s.chal encode).valid c = true) (hS : ScriptShape (fun q : Usize => q.val) c s n_lanes.val)
    (hgs : GrindShape config s)
    (target : NativeReads.F192) (root : Digest) (v : VS) (rest : List NEvent)
    (hroot : ∀ (hl : 0 < s.levels.length), (s.levels[0]'hl).root = root)
    (hv : NativeAnswers out R H leaf node v (s.tape ++ rest))
    (C : Nat → Nat → List U64) (T : Nat → Nat → Nat → Digest)
    (hT0 : ∀ j (hj : j < s.levels.length) i, T j 0 i =
      leaf (List.replicate (s.levels[j].leafWords - s.levels[j].rowWords)
        ReplaySource.primitives.field.gf2_64.F64.ZERO ++ C j i))
    (hT : ∀ j l i, T j (l + 1) i = node (T j l (2 * i)) (T j l (2 * i + 1)))
    (hroots : ∀ j (hj : j < s.levels.length), s.levels[j].root = T j s.levels[j].depth 0)
    (hC : ∀ j (hj : j < s.levels.length) k, k < 2 ^ s.levels[j].depth → (C j k).length = s.levels[j].rowWords)
    (b : Array Concrete.E) (hb : b.size = 2 ^ c.logN)
    (hz : (b.extract (n_lanes.val * 2 ^ (c.logN - c.folds[0]!)) b.size).all (· == Concrete.E.zero) = true)
    (hcaller : ∀ point : Array Concrete.E, point.size = c.logN → callerAt point = Concrete.mle b point) :
    ∃ r v', ReplaySource.whir.verify.verify nativeInst W v config log_n n_lanes target root weight_at = .ok (r, v') ∧
      (r = .Ok () → Protocol.verify c (s.chal encode) n_lanes.val
        (tableOf encodeK ofLimbs true (depthOf s 0) (C 0)) b (encode target)
        (withOracles (s.prf encode encodeK ofLimbs)
          fun j => tableOf encodeK ofLimbs (j == 0) (depthOf s j) (C j)) = .ok ()) := by
  obtain ⟨r, v', hver, hiff⟩ := verify_eq_native encode const encodeK ofLimbs (fun q : Usize => q.val) hw h hr hn
    hD hH hR hP henc W weight_at callerAt hcall config c log_n hcfg s n_lanes hch hS hgs target root v
    rest hroot hv
  refine ⟨r, v', hver, fun hok => ?_⟩
  have hnv := hiff.mp hok
  have hc : c.valid = true := WHIRNativeGuards.challenges_config c _ hch
  obtain ⟨hl0, hl1⟩ := nativeVerify_lanes _ _ _ _ _ _ hnv
  rw [← nativeVerify_withOracles c (s.chal encode) n_lanes.val (encode target) callerAt _
    (fun j => tableOf encodeK ofLimbs (j == 0) (depthOf s j) (C j))] at hnv
  refine nativeVerify_refines c (s.chal encode) n_lanes.val (encode target) callerAt _ b _ ?_
    (root_shape encodeK ofLimbs c s _ hS hc C hC) (root_shapes encodeK ofLimbs c s _ hS C hC _)
    (authenticated_native encode encodeK ofLimbs c s _ hS leaf node hleaf hnode C T hT0 hT hroots
      (level_hints s v rest hv)) hcaller hnv
  simp only [Protocol.shapeValid, hc, hz, Bool.and_true, Bool.true_and]
  simp only [hb, beq_self_eq_true, Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
  omega

end Refines

end WhirAeneas.Native
