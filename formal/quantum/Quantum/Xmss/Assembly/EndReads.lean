module

public import Quantum.Xmss.Events
public import Quantum.Xmss.Assembly.Template
public import Quantum.Xmss.Assembly.Costs
public import Quantum.Sponge.Reads.Log

@[expose] public section

/-!
# The end of the event-bound game: a win is in the event, up to the read error

Security's debt `endReads`, reduced to a decomposition of the winning runs (`WinDecomp`).

* **Classification for a selection function** (`win_imp_bad_sel`). S7's `win_imp_bad` is stated
  for the honest selections `L.select`; in runtime 2 the randomizer trials read the database, not
  the table's keys, so the transcript's signatures are not `L.signature`. Here the signatures, the
  disclosed positions and the memory's records (`Memory.RecordsSel`) are those of an arbitrary
  selection `S`, the recorded digests decoding to the selected words. `mem_bad_of_agrees` and
  `bad_of_winFacts` put a register whose view holds the verification's reads in `Bad L N` from the
  classical facts of a win (`WinFacts`).
* **No empty decompressed cell** (`noBot_runtimeR`). In the basis where every database cell is
  decompressed (`conjReg`, `run_conjReg`), every port of runtime 2 with record ports is classical
  on the databases except a program call, which resets its cell to the uniform superposition of
  the values; so every branch of every run is supported on databases with no empty cell.
* **Reads recorded** (`readsRecorded`). An operator whose decompressed form is supported on
  databases with no empty cell whose view holds a log has weight at least `1 - readError` on the
  compressed databases whose view holds the log (`hw_sandwich` in the decompressed basis,
  `goodReg_mul_agreeReg_mul_goodReg`).
* **The reduction** (`win_le_of_winDecomp`, `endReads_of_winDecomp`): the win weight is at most
  the event weight plus the read error, given operators covering the win, one per run of the
  final reads, recorded in the decompressed basis and in the event in the compressed basis.

Not here: the construction of `WinDecomp` for the canonical game on good tables (`TableGood`).
-/

open OracleComp OracleSpec

namespace Quantum.Xmss

open Quantum.Sponge HashSig HashSig.OverPermutation LeanXmss Common Common.SufCma
  LeanXmss.RandomPermutationModel
open Verification

local notation "Comp" => OracleComp LeanXmss.HashSpec

/-! ## Signatures of a selection function -/

/-- **A selection function**: for each key of each layer and each message, the selected randomizer
and word (none when the search fails). -/
abbrev SelFn : Type :=
  Layer → KeyIndex → HashInput → Option (Randomizer × Encoding)

namespace HonestTable

variable (L : HonestTable) (S : SelFn)

/-- The layer signature of key `e` of layer `l` on `message` with the selection `S`: the selected
randomizer, the chains opened to the selected word, and the path. -/
def selLayerSignature (l : Layer) (e : KeyIndex) (message : HashInput) :
    Option LayerSignature :=
  (S l e message).map fun sel ↦ ⟨sel.1, fun i ↦ L.chainValue l e i (sel.2 i).val, L.authPath l e⟩

/-- The signature of a request with the selection `S`. -/
def selSignature (req : SigningRequest) : Option Signature :=
  (L.selLayerSignature S bottomLayer (keyIndexOnLayer req.leafIndex bottomLayer)
      (littleEndianBytes 32 req.message)).bind fun bottom ↦
    (L.selLayerSignature S topLayer (keyIndexOnLayer req.leafIndex topLayer)
        (littleEndianBytes 16 (L.bottomRoot req.leafIndex))).map fun top ↦
      ⟨req.leafIndex, fun lay ↦ if lay = bottomLayer then bottom else top⟩

/-- The positions the signature of a request with the selection `S` discloses. -/
def selDisclosedBy (req : SigningRequest) : Set Pos :=
  match S bottomLayer (keyIndexOnLayer req.leafIndex bottomLayer)
      (littleEndianBytes 32 req.message),
    S topLayer (keyIndexOnLayer req.leafIndex topLayer)
      (littleEndianBytes 16 (L.bottomRoot req.leafIndex)) with
  | some bottom, some top =>
      layerDisclosed bottomLayer (keyIndexOnLayer req.leafIndex bottomLayer) bottom.2 ∪
        layerDisclosed topLayer (keyIndexOnLayer req.leafIndex topLayer) top.2
  | _, _ => ∅

/-- The positions disclosed after the requests `reqs` with the selection `S`. -/
def selDisclosures (reqs : List SigningRequest) : Set Pos :=
  {.tree topLayer layerHeight 0} ∪ ⋃ req ∈ reqs, L.selDisclosedBy S req

/-- The honest signatures are those of the honest selection. -/
theorem selSignature_select (req : SigningRequest) :
    L.selSignature L.select req = L.signature req :=
  rfl

theorem selDisclosures_select (reqs : List SigningRequest) :
    L.selDisclosures L.select reqs = L.disclosures reqs :=
  rfl

end HonestTable

/-- `M` records the selections `S` of the signer of `req`: each layer's selected message-digest
input, with a digest decoding to the selected word. -/
def Memory.RecordsSel (M : Memory) (L : HonestTable) (S : SelFn) (req : SigningRequest) : Prop :=
  ∀ l sel, S l (keyIndexOnLayer req.leafIndex l) (layerMessage L req l) = some sel →
    ∃ y, M l (keyIndexOnLayer req.leafIndex l) =
      some (msgInput L.param l (keyIndexOnLayer req.leafIndex l) (layerMessage L req l) sel.1, y) ∧
      Codeword.decode y = some sel.2

/-- The honest records are records of the honest selection. -/
theorem Memory.Records.recordsSel {M : Memory} {L : HonestTable} {req : SigningRequest}
    (h : M.Records L req) : M.RecordsSel L L.select req :=
  fun l sel hs ↦ ⟨_, h l sel hs, L.decode_of_select hs⟩

/-! ## The classification for a selection function -/

section Sel

variable {L : HonestTable} {S : SelFn}

/-- **An opened chain position comes from a signature by its key** (`exists_signed_of_known` for
the selection `S`). -/
theorem exists_signed_of_known_sel {reqs : List SigningRequest} {l : Layer} {e : KeyIndex}
    {i : ChainIndex} {j : ℕ} (h : Known (L.selDisclosures S reqs) (.chain l e i j)) :
    ∃ req ∈ reqs, keyIndexOnLayer req.leafIndex l = e ∧
      ∃ sel, S l e (layerMessage L req l) = some sel ∧ (sel.2 i).val ≤ j := by
  obtain ⟨j', hj', hm⟩ := known_chain h l e i j rfl
  rcases hm with hm | hm
  · simp at hm
  simp only [Set.mem_iUnion] at hm
  obtain ⟨req, hreq, hd⟩ := hm
  refine ⟨req, hreq, ?_⟩
  unfold HonestTable.selDisclosedBy at hd
  rcases hb : S bottomLayer (keyIndexOnLayer req.leafIndex bottomLayer)
      (littleEndianBytes 32 req.message) with _ | b <;>
    rcases ht : S topLayer (keyIndexOnLayer req.leafIndex topLayer)
      (littleEndianBytes 16 (L.bottomRoot req.leafIndex)) with _ | tp <;>
    simp only [hb, ht, Set.mem_empty_iff_false] at hd
  rcases hd with (⟨i', hi'⟩ | ⟨lv, hlv⟩) | (⟨i', hi'⟩ | ⟨lv, hlv⟩)
  · simp only [Pos.chain.injEq] at hi'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hi'
    exact ⟨rfl, b, by rw [layerMessage_bottom]; exact hb, hj'⟩
  · cases hlv
  · simp only [Pos.chain.injEq] at hi'
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hi'
    exact ⟨rfl, tp, by rw [layerMessage_top]; exact ht, hj'⟩
  · cases hlv

variable {Ex : Set Slot} {M : Memory} {D : Dbs X Z} {log : QueryLog SigningOracleSpec}

/-- **A layer reaching the honest root of its tree** (no hit) is the signature of that layer with
the selection `S` by a signed request with the same key, on the same message (`layer_meet`). -/
theorem layer_meet_sel (hM : ∀ r ∈ log, M.RecordsSel L S r.1)
    (hEx : Ex ⊆ Public (L.selDisclosures S (log.map Sigma.fst)))
    (hHeld : ∀ s ∈ Ex, L.HeldIn D s)
    (hvalid : SigningTranscript.NoLeafIndexReused log) (hnb : D ∉ xmssBad L Ex M)
    {l : Layer} {e : KeyIndex} (he : e.val < keyCount l) {msg : HashInput}
    (hmsg : 16 ≤ msg.length ∧ msg.length ≤ 32) {part : LayerSignature}
    (hQ : QueriesSatisfy (viewOut L.perm D) (OnPath L.perm D)
      (layerRootWithHash (m := Comp) L.param l e msg part))
    (hr : evalWithAnswerFn (viewOut L.perm D) (layerRootWithHash (m := Comp) L.param l e msg part) =
      some (L.treeValue l layerHeight (e.val / 2 ^ layerHeight))) :
    ∃ r ∈ log, keyIndexOnLayer r.1.leafIndex l = e ∧ msg = layerMessage L r.1 l ∧
      L.selLayerSignature S l e msg = some part := by
  obtain ⟨x, E, hx, hQm, hQc, hEeq, hQl, hQt, hroot⟩ := layerRoot_spec hQ hr
  obtain ⟨hleaf, hpath⟩ := path_meet hHeld hnb he hQt hroot
  have hE : E = L.endpoints l e := by
    by_contra hne
    apply hnb
    refine mem_xmssBad_of_struct hHeld hQl (slotOf_leaf _ _ l e E) trivial ?_ ?_ ?_
    · exact (L.target_eq_some (s := .leaf l e) he rfl).trans (congrArg some hleaf.symm)
    · intro hh
      exact absurd (digestsPayload_injective (thInput_injective _
        (Option.some.inj (hh.symm.trans (HonestTable.honestInput_leaf he)))).2) hne
    · intro h0 hh0
      obtain rfl := Option.some.inj ((HonestTable.honestInput_leaf he).symm.trans hh0)
      exact (length_leafInput L.param l e (L.endpoints l e)).trans
        (length_leafInput L.param l e E).symm
  have hchain : ∀ i, part.chainValues i = L.chainValue l e i (x i).val ∧
      ∀ h : (x i).val < chainLength - 1, Slot.chain l e ⟨(x i).val, h⟩ i ∈ Ex := by
    intro i
    have hEi : E i = L.chainValue l e i (chainLength - 1) := congrFun hE i
    rw [hEeq i] at hEi
    by_cases h3 : (x i).val < chainLength - 1
    · have hsum : (x i).val + (chainLength - 1 - (x i).val) = chainLength - 1 := by omega
      exact chain_meet hHeld hnb he (a := (x i).val) (n := chainLength - 1 - (x i).val)
        (by omega) (by omega) (hQc i) (hEi.trans (congrArg (L.chainValue l e i) hsum.symm))
    · have h3' : (x i).val = chainLength - 1 := by have := (x i).isLt; omega
      refine ⟨?_, fun h ↦ absurd h h3⟩
      have hv : evalWithAnswerFn (viewOut L.perm D) (recoverChainWithHash (m := Comp) L.param l e
          i (x i) (part.chainValues i)) = part.chainValues i := by
        show evalWithAnswerFn (viewOut L.perm D) (chainWalkWithHash (m := Comp) L.param l e i
          (x i).val (chainLength - 1 - (x i).val) (part.chainValues i)) = _
        rw [h3', Nat.sub_self]
        rfl
      exact hv.symm.trans (hEi.trans (congrArg (L.chainValue l e i) h3'.symm))
  have hvx := Codeword.sum_eq_of_decode hx
  have hknown : ∀ i (h : (x i).val < chainLength - 1),
      Known (L.selDisclosures S (log.map Sigma.fst)) (.chain l e i (x i).val) :=
    fun i h ↦ (hEx ((hchain i).2 h)).2
  obtain ⟨i0, hi0⟩ := Codeword.exists_lt_of_sum hvx
  obtain ⟨req, hreq, hkey, sel, hsel, -⟩ := exists_signed_of_known_sel (hknown i0 hi0)
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hreq
  have hle : ∀ i, sel.2 i ≤ x i := by
    intro i
    by_cases h : (x i).val < chainLength - 1
    · obtain ⟨req', hreq', hkey', sel', hsel', hj⟩ := exists_signed_of_known_sel (hknown i h)
      obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hreq'
      rw [layerMessage_eq_of_key hvalid hr hr' (hkey.trans hkey'.symm), hsel'] at hsel
      obtain rfl := Option.some.inj hsel
      exact hj
    · show (sel.2 i).val ≤ (x i).val
      have := (sel.2 i).isLt
      omega
  have hMr := hM r hr l sel (by rw [hkey]; exact hsel)
  rw [hkey] at hMr
  obtain ⟨y, hMy, hvs⟩ := hMr
  have hxs : sel.2 = x := Codeword.eq_of_le (Codeword.sum_eq_of_decode hvs) hvx hle
  have hmeq : msgInput L.param l e msg part.randomizer =
      msgInput L.param l e (layerMessage L r.1 l) sel.1 := by
    by_contra hne
    apply hnb
    refine mem_xmssBad_of_enc hQm (slotOf_msg _ _ l e msg hmsg.1 _) hMy ?_ hne ?_
    · simp only [msgInput, length_thInput, List.length_append, littleEndianBytes,
        List.length_ofFn]
      omega
    · exact Codeword.eq_of_decode hx (hxs ▸ hvs)
  obtain ⟨-, hpay⟩ := thInput_injective _ hmeq
  obtain ⟨hmsgEq, hρ⟩ := List.append_inj' hpay (by simp only [littleEndianBytes, List.length_ofFn])
  have hρ' : part.randomizer = sel.1 := littleEndianBytes_injective 16 hρ
  refine ⟨r, hr, hkey, hmsgEq, ?_⟩
  have hcv : (fun i ↦ L.chainValue l e i (sel.2 i).val) = part.chainValues :=
    funext fun i ↦ (congrArg (fun y : Encoding ↦ L.chainValue l e i (y i).val) hxs).trans
      ((hchain i).1).symm
  rw [hmsgEq, HonestTable.selLayerSignature, hsel, Option.map_some, hcv, ← hρ', ← hpath]

/-- **A win is a target hit, for a selection function** (`win_imp_bad` with the transcript's
signatures, the disclosures and the memory's records those of the selection `S`). -/
theorem win_imp_bad_sel (L : HonestTable) (S : SelFn) (Ex : Set Slot) (M : Memory) (D : Dbs X Z)
    (log : QueryLog SigningOracleSpec) (forgery : Forgery)
    (hlog : ∀ r ∈ log, r.2 = L.selSignature S r.1) (hM : ∀ r ∈ log, M.RecordsSel L S r.1)
    (hEx : Ex ⊆ Public (L.selDisclosures S (log.map Sigma.fst)))
    (hHeld : ∀ s ∈ Ex, L.HeldIn D s)
    (hwin : SigningTranscript.NoLeafIndexReused log ∧
      ¬SignerReturnedForgery SigningRequest.message log forgery.message forgery.signature)
    (hverify :
      (honestEval D.fill L.perm (schemeWithHashFromSeed.verify L.publicKey forgery)).1 = true)
    (hreads : ∀ e ∈ (honestEval D.fill L.perm (schemeWithHashFromSeed.verify L.publicKey forgery)).2,
      e.HeldBy D) :
    D ∈ xmssBad L Ex M := by
  by_contra hnb
  set H := viewOut L.perm D
  have hv : evalWithAnswerFn H
      (verifyWithHash (m := Comp) L.publicKey forgery.message forgery.signature) = true := by
    rw [fst_honestEval] at hverify
    exact hverify
  have hq : QueriesSatisfy H (OnPath L.perm D)
      (verifyWithHash (m := Comp) L.publicKey forgery.message forgery.signature) := by
    intro q hq e he
    exact hreads e (by rw [snd_honestEval]; exact List.mem_flatMap.2 ⟨q, hq, he⟩)
  set idx := forgery.signature.leafIndex
  simp only [verifyWithHash, evalWithAnswerFn_bind] at hv
  simp only [verifyWithHash] at hq
  obtain ⟨hqb, hq⟩ := queriesSatisfy_bind_iff.1 hq
  split at hv
  · next R hb =>
    rw [hb] at hq
    dsimp only at hq hv
    rw [evalWithAnswerFn_bind] at hv
    obtain ⟨hqt, -⟩ := queriesSatisfy_bind_iff.1 hq
    split at hv
    · next R' ht =>
      simp only [evalWithAnswerFn_pure, decide_eq_true_eq] at hv
      have he1 := keyIndexOnLayer_lt idx topLayer
      have hdiv1 : (keyIndexOnLayer idx topLayer).val / 2 ^ layerHeight = 0 :=
        Nat.div_eq_of_lt he1
      have hrt : evalWithAnswerFn H (layerRootWithHash (m := Comp) L.param topLayer
          (keyIndexOnLayer idx topLayer) (littleEndianBytes 16 R)
            (forgery.signature.layers topLayer)) =
          some (L.treeValue topLayer layerHeight
            ((keyIndexOnLayer idx topLayer).val / 2 ^ layerHeight)) := by
        rw [hdiv1]
        exact ht.trans (congrArg some hv)
      obtain ⟨r1, -, hkey1, hmsg1, hsig1⟩ := layer_meet_sel hM hEx hHeld hwin.1 hnb he1
        ⟨(length_littleEndianBytes 16 R).ge,
          (length_littleEndianBytes 16 R).le.trans (by norm_num)⟩
        hqt hrt
      rw [layerMessage_top] at hmsg1
      have hR : R = L.treeValue bottomLayer layerHeight (keyIndexOnLayer idx topLayer).val := by
        rw [littleEndianBytes_injective 16 hmsg1, HonestTable.bottomRoot, hkey1]
      have he0 := keyIndexOnLayer_lt idx bottomLayer
      have hdiv0 : (keyIndexOnLayer idx bottomLayer).val / 2 ^ layerHeight =
          (keyIndexOnLayer idx topLayer).val := by
        simp [keyIndexOnLayer, bottomLayer, topLayer, layerHeight]
      have hrb : evalWithAnswerFn H (layerRootWithHash (m := Comp) L.param bottomLayer
          (keyIndexOnLayer idx bottomLayer) (littleEndianBytes 32 forgery.message)
          (forgery.signature.layers bottomLayer)) =
          some (L.treeValue bottomLayer layerHeight
            ((keyIndexOnLayer idx bottomLayer).val / 2 ^ layerHeight)) := by
        rw [hdiv0, ← hR]
        exact hb
      obtain ⟨r0, hr0, hkey0, hmsg0, hsig0⟩ := layer_meet_sel hM hEx hHeld hwin.1 hnb he0
        ⟨(length_littleEndianBytes 32 _).ge.trans' (by norm_num),
          (length_littleEndianBytes 32 _).le⟩ hqb hrb
      rw [layerMessage_bottom] at hmsg0
      have hidx : r0.1.leafIndex = idx := Fin.ext (by
        have := congrArg Fin.val hkey0
        simpa [keyIndexOnLayer, bottomLayer] using this)
      have hm : r0.1.message = forgery.message := (littleEndianBytes_injective 32 hmsg0).symm
      have hsig : L.selSignature S r0.1 = some forgery.signature := by
        rw [HonestTable.selSignature, hidx, hm, hsig0, Option.bind_some,
          show L.bottomRoot idx = R from hR.symm, hsig1, Option.map_some, signature_eq_layers]
      exact hwin.2 ⟨r0, hr0, hm, (hlog r0 hr0).trans hsig⟩
    · simp at hv
  · simp at hv

end Sel

/-! ## Good tables, and a win with recorded reads is in the event -/

/-- The cell a read reads. -/
def _root_.Quantum.Sponge.SpongeRead.point {X Z : Type} : SpongeRead X Z → SpongeQuery X Z
  | .h z _ => .h z
  | .k x _ => .k x
  | .k' x _ => .k' x

/-- **The honest paths of distinct table slots share no cell.** Then a slot whose honest path the
programmed cells hold with their honest values is one of the programmed (public) slots. -/
def HonestPathsDisjoint (L : HonestTable) : Prop :=
  ∀ s s' i i', InTable s → InTable s' → s ≠ s' → L.honestInput s = some i →
    L.honestInput s' = some i' → ∀ e ∈ inputReads L.keys L.perm i,
      ∀ e' ∈ inputReads L.keys L.perm i', e.point ≠ e'.point

/-- **The good tables of `endReads`**: `PermGood L.perm 18` (as the event bound) and honest paths
sharing no cell. -/
def TableGood (L : HonestTable) : Prop :=
  PermGood L.perm 18 ∧ HonestPathsDisjoint L

/-- **A win with recorded reads is in the event** (`win_imp_bad_sel` on the union of the
hardwired cells and the databases): if the view `hwView W D` holds the log of the verification's
reads, whose honest evaluation on any database holding them accepts the forgery with its reads held,
against a transcript of signatures of the selection `S` recorded in the selections `m`, and the
exempted slots of `W` are public, then `(D, W, m)` is in `Bad L N`. -/
theorem mem_bad_of_agrees (L : HonestTable) {N : ℕ} (S : SelFn) {D : DbReg X Z} {W : Hw X Z}
    {m : Selections} (log : QueryLog (spongeOSpec X Z)) (siglog : QueryLog SigningOracleSpec)
    (forgery : Forgery) (hN : dbGrade W ≤ N)
    (hlog : ∀ r ∈ siglog, r.2 = L.selSignature S r.1)
    (hM : ∀ r ∈ siglog, m.toMemory.RecordsSel L S r.1)
    (hEx : exOf L W ⊆ Public (L.selDisclosures S (siglog.map Sigma.fst)))
    (hwin : SigningTranscript.NoLeafIndexReused siglog ∧
      ¬SignerReturnedForgery SigningRequest.message siglog forgery.message forgery.signature)
    (hverify : ∀ U : Dbs X Z, (∀ e ∈ log.map toSpongeRead, e.HeldBy U) →
      (honestEval U.fill L.perm (schemeWithHashFromSeed.verify L.publicKey forgery)).1 = true ∧
        ∀ e ∈ (honestEval U.fill L.perm (schemeWithHashFromSeed.verify L.publicKey forgery)).2,
          e.HeldBy U)
    (hag : DbReg.Agrees log (hwView W D)) : (D, W, m) ∈ Bad L N := by
  have hU := hverify (union W D) ((agrees_iff_forall_heldBy log (hwView W D)).1 hag)
  exact mem_bad_of hN (win_imp_bad_sel L S (exOf L W) m.toMemory (union W D) siglog forgery hlog hM
    hEx (fun _ hs ↦ heldIn_union_of_mem_exOf D hs) hwin hU.1 hU.2)

/-- **The classical facts of a winning run** at the hardwired cells `W` and selections `m`: few
hardwired cells, the transcript's signatures and the recorded selections are those of the
selection `S`, the exempted slots are public, the forgery is not a returned signature of a valid
transcript, and the verification's reads `log` make its honest evaluation accept with its reads
held. -/
structure WinFacts (L : HonestTable) (N : ℕ) (S : SelFn) (log : QueryLog (spongeOSpec X Z))
    (siglog : QueryLog SigningOracleSpec) (forgery : Forgery) (W : Hw X Z) (m : Selections) :
    Prop where
  grade : dbGrade W ≤ N
  sigs : ∀ r ∈ siglog, r.2 = L.selSignature S r.1
  records : ∀ r ∈ siglog, m.toMemory.RecordsSel L S r.1
  exempt : exOf L W ⊆ Public (L.selDisclosures S (siglog.map Sigma.fst))
  win : SigningTranscript.NoLeafIndexReused siglog ∧
    ¬SignerReturnedForgery SigningRequest.message siglog forgery.message forgery.signature
  verify : ∀ U : Dbs X Z, (∀ e ∈ log.map toSpongeRead, e.HeldBy U) →
    (honestEval U.fill L.perm (schemeWithHashFromSeed.verify L.publicKey forgery)).1 = true ∧
      ∀ e ∈ (honestEval U.fill L.perm (schemeWithHashFromSeed.verify L.publicKey forgery)).2,
        e.HeldBy U

/-- `Bad L N` on the register whose memory also carries a label (Security's `BadR`). -/
def BadRS {S : Type} (L : HonestTable) (N : ℕ) : Set (HwReg X Z (Finset S × Selections)) :=
  {r | (r.1, r.2.1, r.2.2.2) ∈ Bad L N}

/-- **The event part of a decomposition from the classical facts**: an operator supported on
registers with the classical facts of a win is supported where a view holding the log is in
`BadRS`. -/
theorem bad_of_winFacts {S A : Type} (L : HonestTable) (N : ℕ) (Sel : SelFn)
    (log : QueryLog (spongeOSpec X Z)) (siglog : QueryLog SigningOracleSpec) (forgery : Forgery)
    {σ : Matrix (A × HwReg X Z (Finset S × Selections)) (A × HwReg X Z (Finset S × Selections)) ℂ}
    (h : QuerySupportedOn (fun y : A × HwReg X Z (Finset S × Selections) ↦ y.2)
      {s | WinFacts L N Sel log siglog forgery s.2.1 s.2.2.2} σ) :
    QuerySupportedOn (fun y : A × HwReg X Z (Finset S × Selections) ↦ y.2)
      {s | DbReg.Agrees log (hwView s.2.1 s.1) → s ∈ BadRS L N} σ :=
  h.mono fun _ hs hag ↦ mem_bad_of_agrees L Sel log siglog forgery hs.grade hs.sigs hs.records
    hs.exempt hs.win hs.verify hag

end Quantum.Xmss

/-! ## A runtime in a conjugated basis of its register -/

namespace Quantum.Xmss.Assembly

open Quantum Quantum.Sponge Matrix
open scoped Kronecker ComplexOrder

section conjReg

variable {spec : QuantumOracleSpec.{0, 0}} (R : QuantumRuntime spec) (C : Matrix R.D R.D ℂ)
  (hC : C * C = 1) (hCh : Cᴴ = C)

include hC hCh in
theorem trace_conj_one_kronecker {E : Type} [Fintype E] [DecidableEq E]
    (ρ : Matrix (E × R.D) (E × R.D) ℂ) :
    (MatrixMap.conj ((1 : Matrix E E ℂ) ⊗ₖ C) ρ).trace = ρ.trace := by
  rw [MatrixMap.trace_conj_apply, conjTranspose_kronecker, conjTranspose_one, hCh,
    ← mul_kronecker_mul, Matrix.one_mul, hC, one_kronecker_one, Matrix.one_mul]

include hC in
theorem conj_one_kronecker_comp_self {E : Type} [Fintype E] [DecidableEq E] :
    MatrixMap.conj ((1 : Matrix E E ℂ) ⊗ₖ C) ∘ₗ MatrixMap.conj ((1 : Matrix E E ℂ) ⊗ₖ C) =
      LinearMap.id := by
  rw [← MatrixMap.conj_mul, ← mul_kronecker_mul, Matrix.one_mul, hC, one_kronecker_one,
    MatrixMap.conj_one]

/-- **The runtime in the basis conjugated by `C`**: every branch conjugated by `id ⊗ C` on both
sides (`C` a Hermitian involution). -/
@[reducible]
noncomputable def conjReg : QuantumRuntime spec where
  D := R.D
  init := R.init
  step i := SubInstrument.ofIsTNISum
    (fun r ↦ MatrixMap.conj ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ C) ∘ₗ
      (R.step i).branch r ∘ₗ MatrixMap.conj ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ C))
    (fun r ↦ ((MatrixMap.isCP_conj _).comp ((R.step i).isCP_branch r)).comp
      (MatrixMap.isCP_conj _))
    fun s ρ hρ ↦ by
      have hρ' := (MatrixMap.isCP_conj ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ C)).posSemidef hρ
      have h := (R.step i).isTNI_sum s _ hρ'
      have e : (∑ a ∈ s, MatrixMap.conj ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ C) ∘ₗ
          (R.step i).branch a ∘ₗ MatrixMap.conj ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ C)) ρ =
          MatrixMap.conj ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ C)
            ((∑ a ∈ s, (R.step i).branch a)
              (MatrixMap.conj ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ C) ρ)) := by
        simp only [LinearMap.sum_apply, LinearMap.comp_apply, map_sum]
      rw [e, trace_conj_one_kronecker R C hC hCh]
      exact h.trans_eq (by rw [trace_conj_one_kronecker R C hC hCh])

theorem conjReg_branch (i : spec.Port) (r : spec.Result i) :
    ((conjReg R C hC hCh).step i).branch r =
      MatrixMap.conj ((1 : Matrix (spec.Out i) (spec.Out i) ℂ) ⊗ₖ C) ∘ₗ (R.step i).branch r ∘ₗ
        MatrixMap.conj ((1 : Matrix (spec.In i) (spec.In i) ℂ) ⊗ₖ C) :=
  rfl

/-- **Simulation in the conjugated basis**: running in `conjReg` from the conjugated operator is
the conjugated run. -/
theorem run_conjReg {L : LocalSig.{0, 0}} (I : L.Interp) {W : QReg → Type} {A : QReg}
    (x : QuantumComp L spec W A) (p : Σ u, W u) (ρ : Matrix (A × R.D) (A × R.D) ℂ) :
    ((conjReg R C hC hCh).run I x).branch p
        (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ C) ρ) =
      MatrixMap.conj ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ C) ((R.run I x).branch p ρ) := by
  have h := QuantumRuntime.simulation I (R₁ := R) (R₂ := conjReg R C hC hCh)
    (V := MatrixMap.conj C) (fun i r ↦ by
      rw [MatrixMap.amplifyLeft_conj, MatrixMap.amplifyLeft_conj, conjReg_branch R C hC hCh,
        LinearMap.comp_assoc, LinearMap.comp_assoc, conj_one_kronecker_comp_self R C hC,
        LinearMap.comp_id]) x p
  have h' := LinearMap.congr_fun h ρ
  rw [LinearMap.comp_apply, LinearMap.comp_apply, MatrixMap.amplifyLeft_conj,
    MatrixMap.amplifyLeft_conj] at h'
  exact h'

end conjReg

/-! ## Support invariants along a run -/

section supp

variable {spec : QuantumOracleSpec.{0, 0}} (R : QuantumRuntime spec) (P : Set R.D)

/-- **One call keeps a support invariant of the runtime register** when every step does. -/
theorem querySupportedOn_queryStep
    (hR : ∀ i r (σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ),
      QuerySupportedOn (fun m : spec.In i × R.D ↦ m.2) P σ →
        QuerySupportedOn (fun m : spec.Out i × R.D ↦ m.2) P ((R.step i).branch r σ))
    {A : QReg} (i : spec.Port) (E : QReg) (ℓ : A ≃ spec.In i × E) (r : spec.Result i)
    {ρ : Matrix (A × R.D) (A × R.D) ℂ}
    (h : QuerySupportedOn (fun m : A × R.D ↦ m.2) P ρ) :
    QuerySupportedOn (fun m : (spec.Out i × E) × R.D ↦ m.2) P
      ((R.queryStep i E ℓ).branch r ρ) := by
  rw [QuantumRuntime.queryStep_branch_apply, DSubInstrument.branch_frame_apply]
  have h₁ := (h.branch_relabel (QuantumRuntime.queryEquivIn ℓ R.D)).imp
    (q' := fun m : (spec.In i × R.D) × E ↦ m.1.2) (S' := P) fun m hm ↦ by
      obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivIn ℓ R.D).surjective m
      rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm
  have h₂ := QuerySupportedOn.amplify_fst (q := fun m : spec.In i × R.D ↦ m.2)
    (q' := fun m : spec.Out i × R.D ↦ m.2) (fun σ hσ ↦ hR i r σ hσ) h₁
  refine (h₂.branch_relabel (QuantumRuntime.queryEquivOut _ R.D E)).imp fun m hm ↦ ?_
  obtain ⟨y, rfl⟩ := (QuantumRuntime.queryEquivOut _ R.D E).surjective m
  rwa [Function.comp_apply, Equiv.symm_apply_apply] at hm

/-- **A support invariant of the runtime register along a run**: if every step keeps the support
in `P`, every branch of every run does. -/
theorem querySupportedOn_run
    (hR : ∀ i r (σ : Matrix (spec.In i × R.D) (spec.In i × R.D) ℂ),
      QuerySupportedOn (fun m : spec.In i × R.D ↦ m.2) P σ →
        QuerySupportedOn (fun m : spec.Out i × R.D ↦ m.2) P ((R.step i).branch r σ))
    {L : LocalSig.{0, 0}} (I : L.Interp) {W : QReg → Type} {A : QReg}
    (x : QuantumComp L spec W A) {ρ : Matrix (A × R.D) (A × R.D) ℂ}
    (hρ : QuerySupportedOn (fun m : A × R.D ↦ m.2) P ρ) (p : Σ u, W u) :
    QuerySupportedOn (fun m : p.1 × R.D ↦ m.2) P ((R.run I x).branch p ρ) := by
  classical
  induction x using QuantumComp.inductionOn with
  | pure _ y =>
    rw [QuantumRuntime.run_pure]
    by_cases hp : p = ⟨_, y⟩
    · subst hp
      rw [DSubInstrument.branch_ret_self]
      exact hρ
    · rw [DSubInstrument.branch_ret_of_ne _ hp]
      exact querySupportedOn_zero _ _
  | primBind _ o k ih =>
    rw [QuantumRuntime.run_primBind, DSubInstrument.branch_bind_apply]
    exact QuerySupportedOn.tsum fun c ↦ ih c (QuerySupportedOn.amplify_snd (q := id) hρ _)
  | queryBind _ i E ℓ k ih =>
    rw [QuantumRuntime.run_queryBind, DSubInstrument.branch_bind_apply]
    exact QuerySupportedOn.tsum fun r ↦ ih r (querySupportedOn_queryStep R P hR i E ℓ r hρ)

end supp


/-! ## The ports of the hardwired runtime in the decompressed basis -/

section cell

variable {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y]

omit [DecidableEq A] [DecidableEq Y] in
theorem kron_one_mul_clsKraus {T B : Type} [Fintype T] [Fintype B] [DecidableEq B]
    (V : Matrix T T ℂ) (p : B → Prop) [DecidablePred p] (φ : B → B) (R : B → Matrix T T ℂ) :
    (V ⊗ₖ (1 : Matrix B B ℂ)) * clsKraus p φ R = clsKraus p φ fun b ↦ V * R b := by
  ext ⟨s', b'⟩ ⟨s, b⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [kroneckerMap_apply, Matrix.one_apply, clsKraus_apply]
  have key : ∀ t, ∑ c, V s' t * (if b' = c then (1 : ℂ) else 0) *
      (if p b ∧ c = φ b then R b t s else 0) = if p b ∧ b' = φ b then V s' t * R b t s else 0 := by
    intro t
    rw [Finset.sum_eq_single b' (fun c _ hc ↦ by simp [Ne.symm hc]) (by simp)]
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl fun t _ ↦ key t]
  split_ifs <;> simp [Matrix.mul_apply]

omit [DecidableEq A] [DecidableEq Y] in
theorem clsKraus_mul_kron_one {T B : Type} [Fintype T] [Fintype B] [DecidableEq B]
    (V : Matrix T T ℂ) (p : B → Prop) [DecidablePred p] (φ : B → B) (R : B → Matrix T T ℂ) :
    clsKraus p φ R * (V ⊗ₖ (1 : Matrix B B ℂ)) = clsKraus p φ fun b ↦ R b * V := by
  ext ⟨s', b'⟩ ⟨s, b⟩
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [kroneckerMap_apply, Matrix.one_apply, clsKraus_apply]
  have key : ∀ t, ∑ c, (if p c ∧ b' = φ c then R c s' t else 0) * (V t s *
      (if c = b then (1 : ℂ) else 0)) = if p b ∧ b' = φ b then R b s' t * V t s else 0 := by
    intro t
    rw [Finset.sum_eq_single b (fun c _ hc ↦ by simp [hc]) (by simp)]
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl fun t _ ↦ key t]
  split_ifs <;> simp [Matrix.mul_apply]

omit [DecidableEq A] [DecidableEq Y] in
/-- Conjugating a classical Kraus operator by an operator on its quantum factor. -/
theorem kron_one_mul_clsKraus_mul_kron_one {T B : Type} [Fintype T] [Fintype B] [DecidableEq B]
    (V : Matrix T T ℂ) (p : B → Prop) [DecidablePred p] (φ : B → B) (R : B → Matrix T T ℂ) :
    (V ⊗ₖ (1 : Matrix B B ℂ)) * clsKraus p φ R * (V ⊗ₖ (1 : Matrix B B ℂ)) =
      clsKraus p φ fun b ↦ V * R b * V := by
  rw [kron_one_mul_clsKraus, clsKraus_mul_kron_one]

omit [Fintype Y] in
/-- The compressed cell-`a` discard as a pi-tensor product: `|⊥⟩⟨o|` at `a`. -/
theorem cellDiscard_eq_piKron (a : A) (o : Option Y) :
    cellDiscard (Y := Y) a o =
      piKron (Function.update (fun _ ↦ (1 : Matrix (Option Y) (Option Y) ℂ)) a
        (Matrix.of fun u u' ↦ if u = none ∧ u' = o then 1 else 0)) := by
  ext D' D
  rw [piKron_apply, Fintype.prod_eq_mul_prod_compl a, Function.update_self]
  have hrest : ∏ x ∈ ({a}ᶜ : Finset A), Function.update
      (fun _ ↦ (1 : Matrix (Option Y) (Option Y) ℂ)) a
        (Matrix.of fun u u' ↦ if u = none ∧ u' = o then 1 else 0) x (D' x) (D x) =
      if ∀ x ∈ ({a}ᶜ : Finset A), D' x = D x then 1 else 0 := by
    by_cases h : ∀ x ∈ ({a}ᶜ : Finset A), D' x = D x
    · simp only [eq_true h, ↓reduceIte]
      refine Finset.prod_eq_one fun x hx ↦ ?_
      rw [Function.update_of_ne (by simpa using hx), h x hx, Matrix.one_apply_eq]
    · simp only [eq_false h, ↓reduceIte]
      simp only [not_forall] at h
      obtain ⟨x, hx, hne⟩ := h
      exact Finset.prod_eq_zero hx (by
        rw [Function.update_of_ne (by simpa using hx), Matrix.one_apply_ne hne])
  rw [hrest, cellDiscard, of_apply, of_apply]
  by_cases h : D a = o ∧ D' = Function.update D a none
  · obtain ⟨h1, rfl⟩ := h
    simp [h1]
    exact fun x hx ↦ Function.update_of_ne hx _ _
  · simp only [h, ↓reduceIte]
    by_cases h1 : D' a = none ∧ D a = o
    · have h2 : ¬ ∀ x ∈ ({a}ᶜ : Finset A), D' x = D x := fun h2 ↦ h ⟨h1.2, funext fun x ↦ by
        by_cases hx : x = a
        · subst hx
          rw [Function.update_self, h1.1]
        · rw [Function.update_of_ne hx, h2 x (by simpa using hx)]⟩
      simp only [eq_false h2, ↓reduceIte, mul_zero]
    · simp only [h1, ↓reduceIte, zero_mul]

variable [Nonempty Y]

/-- **A read in the decompressed basis is classical**: the projector on the databases whose cell
`a`, overwritten by the hardwired value, is `o`. -/
theorem compressAll_mul_cellRead_mul_compressAll (w : Database A Y) (a : A) (o : Option Y) :
    compressAll A Y * cellRead w a o * compressAll A Y =
      diagonal fun D : Database A Y ↦ if (w a).or (D a) = o then (1 : ℂ) else 0 := by
  rcases hw : w a with _ | v
  · have hr : cellRead w a o = compressAll A Y *
        (diagonal fun D : Database A Y ↦ if D a = o then (1 : ℂ) else 0) * compressAll A Y := by
      rw [← compressAt_mul_diagonal_cell_mul_compressAt]
      simp [cellRead, hw]
    rw [hr, ← Matrix.mul_assoc, ← Matrix.mul_assoc, compressAll_mul_self, Matrix.one_mul,
      Matrix.mul_assoc, compressAll_mul_self, Matrix.mul_one]
    congr 1
  · have hr : cellRead w a o = if o = some v then 1 else 0 := by simp [cellRead, hw]
    rw [hr]
    by_cases ho : o = some v
    · subst ho
      simp [compressAll_mul_self]
    · have ho' : ¬ some v = o := fun h ↦ ho h.symm
      simp [ho, ho']

/-- **A discard in the decompressed basis**: it keeps every other cell and leaves cell `a`
holding a value (the uniform superposition of the values). -/
theorem compressAll_mul_cellDiscard_mul_compressAll_ne_zero {a : A} {o : Option Y}
    {D' D : Database A Y}
    (h : (compressAll A Y * cellDiscard a o * compressAll A Y) D' D ≠ 0) :
    (∀ b, b ≠ a → D' b = D b) ∧ (D' a).isSome := by
  rw [cellDiscard_eq_piKron, compressAll, piKron_mul, piKron_mul, piKron_apply] at h
  have hf := Finset.prod_ne_zero_iff.mp h
  refine ⟨fun b hb ↦ ?_, ?_⟩
  · have hb' := hf b (Finset.mem_univ b)
    rw [Function.update_of_ne hb, Matrix.mul_one, cellCompress_mul_self] at hb'
    by_contra hne
    exact hb' (Matrix.one_apply_ne hne)
  · have ha := hf a (Finset.mem_univ a)
    rw [Function.update_self] at ha
    simp only [Matrix.mul_apply, of_apply, mul_ite, mul_one, mul_zero] at ha
    rcases hD : D' a with _ | y
    · rw [hD] at ha
      simp at ha
    · rfl

end cell

/-! ## No empty decompressed cell in runtime 2 with record ports -/

section noBot

open Quantum.Xmss.Hybrid

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-- Every cell of the three databases holds a value. -/
def NoBotDb (D : DbReg X Z) : Prop :=
  (∀ z, (D.1 z).isSome) ∧ (∀ x, (D.2.1 x).isSome) ∧ ∀ x, (D.2.2 x).isSome

/-- An operator on one database whose nonzero entries lead from databases with no empty cell to
databases with no empty cell. -/
def CellKeeps {A Y : Type} (N : Matrix (Database A Y) (Database A Y) ℂ) : Prop :=
  ∀ D' D, N D' D ≠ 0 → (∀ a, (D a).isSome) → ∀ a, (D' a).isSome

/-- An operator on the three databases whose nonzero entries keep `NoBotDb`. -/
def KeepsNoBot (N : Matrix (DbReg X Z) (DbReg X Z) ℂ) : Prop :=
  ∀ D' D, N D' D ≠ 0 → NoBotDb D → NoBotDb D'

theorem cellKeeps_diagonal {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y]
    (f : Database A Y → ℂ) : CellKeeps (diagonal f) := by
  intro D' D h hD
  by_cases he : D' = D
  · subst he
    exact hD
  · exact absurd (diagonal_apply_ne f he) h

theorem cellKeeps_one {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y] :
    CellKeeps (1 : Matrix (Database A Y) (Database A Y) ℂ) := by
  rw [← diagonal_one]
  exact cellKeeps_diagonal _

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
theorem keepsNoBot_kron {N₁ : Matrix (Database Z X) (Database Z X) ℂ}
    {N₂ N₃ : Matrix (Database X Z) (Database X Z) ℂ} (h₁ : CellKeeps N₁) (h₂ : CellKeeps N₂)
    (h₃ : CellKeeps N₃) : KeepsNoBot (N₁ ⊗ₖ (N₂ ⊗ₖ N₃)) := by
  intro D' D h hD
  rw [kroneckerMap_apply, kroneckerMap_apply] at h
  exact ⟨h₁ _ _ (left_ne_zero_of_mul h) hD.1, h₂ _ _ (left_ne_zero_of_mul (right_ne_zero_of_mul h))
    hD.2.1, h₃ _ _ (right_ne_zero_of_mul (right_ne_zero_of_mul h)) hD.2.2⟩

variable [Nonempty X] [Nonempty Z] [AddCommGroup X] [AddCommGroup Z]

omit [Nonempty X] [Nonempty Z] [AddCommGroup X] [AddCommGroup Z] in
theorem compressDbs_mul_kron_mul_compressDbs (N₁ : Matrix (Database Z X) (Database Z X) ℂ)
    (N₂ N₃ : Matrix (Database X Z) (Database X Z) ℂ) :
    compressDbs X Z * (N₁ ⊗ₖ (N₂ ⊗ₖ N₃)) * compressDbs X Z =
      (compressAll Z X * N₁ * compressAll Z X) ⊗ₖ ((compressAll X Z * N₂ * compressAll X Z) ⊗ₖ
        (compressAll X Z * N₃ * compressAll X Z)) := by
  simp only [compressDbs, ← mul_kronecker_mul]

theorem cellKeeps_compressAll_one {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y]
    [DecidableEq Y] [Nonempty Y] :
    CellKeeps (compressAll A Y * 1 * compressAll A Y) := by
  rw [Matrix.mul_one, compressAll_mul_self]
  exact cellKeeps_one (A := A) (Y := Y)

theorem cellKeeps_compressAll_cellRead {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y]
    [DecidableEq Y] [Nonempty Y] (w : Database A Y) (a : A) (o : Option Y) :
    CellKeeps (compressAll A Y * cellRead w a o * compressAll A Y) := by
  rw [compressAll_mul_cellRead_mul_compressAll]
  exact cellKeeps_diagonal (A := A) (Y := Y) _

theorem cellKeeps_compressAll_cellDiscard {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y]
    [DecidableEq Y] [Nonempty Y] (a : A) (o : Option Y) :
    CellKeeps (compressAll A Y * cellDiscard a o * compressAll A Y) := by
  intro D' D h hD b
  obtain ⟨h₁, h₂⟩ := compressAll_mul_cellDiscard_mul_compressAll_ne_zero h
  by_cases hb : b = a
  · subst hb
    exact h₂
  · rw [h₁ b hb]
    exact hD b

omit [Nonempty X] [Nonempty Z] in
theorem keepsNoBot_one : KeepsNoBot (compressDbs X Z * 1 * compressDbs X Z) := by
  rw [Matrix.mul_one, compressDbs_mul_self, ← one_kronecker_one, ← one_kronecker_one]
  exact keepsNoBot_kron (cellKeeps_one (A := Z) (Y := X)) (cellKeeps_one (A := X) (Y := Z))
    (cellKeeps_one (A := X) (Y := Z))

omit [Nonempty X] [Nonempty Z] [AddCommGroup X] [AddCommGroup Z] in
theorem keepsNoBot_of_cells {N₁ : Matrix (Database Z X) (Database Z X) ℂ}
    {N₂ N₃ : Matrix (Database X Z) (Database X Z) ℂ}
    (h₁ : CellKeeps (compressAll Z X * N₁ * compressAll Z X))
    (h₂ : CellKeeps (compressAll X Z * N₂ * compressAll X Z))
    (h₃ : CellKeeps (compressAll X Z * N₃ * compressAll X Z)) :
    KeepsNoBot (compressDbs X Z * (N₁ ⊗ₖ (N₂ ⊗ₖ N₃)) * compressDbs X Z) := by
  rw [compressDbs_mul_kron_mul_compressDbs]
  exact keepsNoBot_kron h₁ h₂ h₃

variable {M' : Type} [Fintype M'] [DecidableEq M']

/-- The databases of a register have no empty cell. -/
def NoBot (s : HwReg X Z M') : Prop :=
  NoBotDb s.1

omit [Nonempty X] [Nonempty Z] [AddCommGroup X] [AddCommGroup Z] in
/-- A classical Kraus operator of the hardwired register, in the decompressed basis, keeps
`NoBot` when its database operators do. -/
theorem noBot_of_clsKraus (p : Hw X Z × M' → Prop) {_ : DecidablePred p} (φ : Hw X Z × M' → Hw X Z × M')
    (R : Hw X Z × M' → Matrix (DbReg X Z) (DbReg X Z) ℂ)
    (hR : ∀ b, KeepsNoBot (compressDbs X Z * R b * compressDbs X Z)) (m' m : Unit × HwReg X Z M')
    (h : (((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z M') *
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ clsKraus p φ R) *
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z M')) m' m ≠ 0) (hm : NoBot m.2) :
    NoBot m'.2 := by
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul, compressReg,
    kron_one_mul_clsKraus_mul_kron_one] at h
  have h' := (one_kronecker_ne_zero (a := m.1) (a' := m'.1) (b := m.2) (b' := m'.2) h).2
  rw [clsKraus_apply] at h'
  split_ifs at h' with hc
  · exact hR _ _ _ h' hm
  · exact absurd rfl h'

omit [Nonempty X] [Nonempty Z] in
theorem one_kron_mul_hwPort_mul_one_kron {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y]
    [DecidableEq Y] [AddCommGroup Y] (read : HwReg X Z M' → A → Y) :
    ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressReg X Z M') * hwPort read *
        ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressReg X Z M') = tableOracle read := by
  have hCC : ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressReg X Z M') *
      ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressReg X Z M') = 1 := by
    rw [← mul_kronecker_mul, Matrix.one_mul, compressReg_mul_self, one_kronecker_one]
  rw [hwPort, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hCC, Matrix.one_mul, Matrix.mul_assoc,
    hCC, Matrix.mul_one]

omit [Nonempty X] [Nonempty Z] [Fintype M'] [AddCommGroup X] [AddCommGroup Z] in
theorem noBot_of_tableOracle {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y]
    [DecidableEq Y] [AddCommGroup Y] (read : HwReg X Z M' → A → Y)
    (m' m : (A × Y) × HwReg X Z M') (h : tableOracle read m' m ≠ 0) (hm : NoBot m.2) :
    NoBot m'.2 := by
  rw [tableOracle_apply] at h
  split_ifs at h with he
  · rw [he]
    exact hm
  · exact absurd rfl h

omit [Nonempty X] [Nonempty Z] in
theorem noBot_of_hwPort {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y]
    [DecidableEq Y] [AddCommGroup Y] (read : HwReg X Z M' → A → Y)
    (m' m : (A × Y) × HwReg X Z M')
    (h : (((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressReg X Z M') * hwPort read *
      ((1 : Matrix (A × Y) (A × Y) ℂ) ⊗ₖ compressReg X Z M')) m' m ≠ 0) (hm : NoBot m.2) :
    NoBot m'.2 := by
  rw [one_kron_mul_hwPort_mul_one_kron] at h
  exact noBot_of_tableOracle read m' m h hm

variable {S : Type} [Fintype S] [DecidableEq S] {M : Type} [Fintype M] [DecidableEq M]

/-- Runtime 2 with record ports, its register written as the hardwired register. -/
@[reducible]
noncomputable def runtimeRH (m₀ : Finset S × M) : QuantumRuntime (recHwSpec X Z S M) where
  D := QReg.of (HwReg X Z (Finset S × M))
  init := (runtimeR m₀).init
  step := (runtimeR m₀).step

/-- Runtime 2 with record ports in the decompressed basis. -/
noncomputable abbrev decR (m₀ : Finset S × M) : QuantumRuntime (recHwSpec X Z S M) :=
  conjReg (runtimeRH m₀) (compressReg X Z (Finset S × M)) compressReg_mul_self
    conjTranspose_compressReg

theorem decR_branch_apply (m₀ : Finset S × M) (i : (recHwSpec X Z S M).Port)
    (r : (recHwSpec X Z S M).Result i)
    (K : Matrix ((recHwSpec X Z S M).Out i × HwReg X Z (Finset S × M))
      ((recHwSpec X Z S M).In i × HwReg X Z (Finset S × M)) ℂ)
    (hK : ((runtimeRH m₀).step i).branch r = MatrixMap.conj K)
    (σ : Matrix ((recHwSpec X Z S M).In i × HwReg X Z (Finset S × M))
      ((recHwSpec X Z S M).In i × HwReg X Z (Finset S × M)) ℂ) :
    ((decR m₀).step i).branch r σ = MatrixMap.conj
      (((1 : Matrix ((recHwSpec X Z S M).Out i) ((recHwSpec X Z S M).Out i) ℂ) ⊗ₖ
        compressReg X Z (Finset S × M)) * K *
        ((1 : Matrix ((recHwSpec X Z S M).In i) ((recHwSpec X Z S M).In i) ℂ) ⊗ₖ
          compressReg X Z (Finset S × M))) σ := by
  rw [conjReg_branch, hK, MatrixMap.conj_mul, MatrixMap.conj_mul]
  rfl

/-- **Every step of runtime 2 with record ports keeps `NoBot` in the decompressed basis.** -/
theorem decR_step_noBot (m₀ : Finset S × M) (i : (recHwSpec X Z S M).Port)
    (r : (recHwSpec X Z S M).Result i)
    (σ : Matrix ((recHwSpec X Z S M).In i × HwReg X Z (Finset S × M))
      ((recHwSpec X Z S M).In i × HwReg X Z (Finset S × M)) ℂ)
    (hσ : QuerySupportedOn (fun m : (recHwSpec X Z S M).In i × HwReg X Z (Finset S × M) ↦ m.2)
      {s | NoBot s} σ) :
    QuerySupportedOn (fun m : (recHwSpec X Z S M).Out i × HwReg X Z (Finset S × M) ↦ m.2)
      {s | NoBot s} (((decR m₀).step i).branch r σ) := by
  rcases i with ((i | c) | c) | T
  · rw [decR_branch_apply m₀ _ r _ (runtime2_branch m₀ (.inl (.inl i)) r)]
    refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ ?_
    cases i <;> exact noBot_of_hwPort _ m' m hK hm
  · rw [decR_branch_apply m₀ _ r _ (runtime2_branch m₀ (.inl (.inr c)) r)]
    refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ ?_
    cases c with
    | readH z upd =>
      refine noBot_of_clsKraus _ _ _ (fun b ↦ ?_) m' m hK hm
      rw [← one_kronecker_one]
      exact keepsNoBot_of_cells (cellKeeps_compressAll_cellRead _ _ _) cellKeeps_compressAll_one
        cellKeeps_compressAll_one
    | readK x upd =>
      refine noBot_of_clsKraus _ _ _ (fun b ↦ ?_) m' m hK hm
      exact keepsNoBot_of_cells cellKeeps_compressAll_one (cellKeeps_compressAll_cellRead _ _ _)
        cellKeeps_compressAll_one
    | readK' x upd =>
      refine noBot_of_clsKraus _ _ _ (fun b ↦ ?_) m' m hK hm
      exact keepsNoBot_of_cells cellKeeps_compressAll_one cellKeeps_compressAll_one
        (cellKeeps_compressAll_cellRead _ _ _)
  · rw [decR_branch_apply m₀ _ r _ (runtime2_branch m₀ (.inr c) r)]
    refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ ?_
    cases c with
    | programH z v =>
      refine noBot_of_clsKraus _ _ _ (fun b ↦ ?_) m' m hK hm
      rw [← one_kronecker_one]
      exact keepsNoBot_of_cells (cellKeeps_compressAll_cellDiscard _ _) cellKeeps_compressAll_one
        cellKeeps_compressAll_one
    | programK x v =>
      refine noBot_of_clsKraus _ _ _ (fun b ↦ ?_) m' m hK hm
      exact keepsNoBot_of_cells cellKeeps_compressAll_one (cellKeeps_compressAll_cellDiscard _ _)
        cellKeeps_compressAll_one
    | programK' x v =>
      refine noBot_of_clsKraus _ _ _ (fun b ↦ ?_) m' m hK hm
      exact keepsNoBot_of_cells cellKeeps_compressAll_one cellKeeps_compressAll_one
        (cellKeeps_compressAll_cellDiscard _ _)
  · rw [decR_branch_apply m₀ _ r _ (recStep_branch T r)]
    refine QuerySupportedOn.conj hσ fun m' m hK hm ↦ ?_
    exact noBot_of_clsKraus _ _ _ (fun _ ↦ keepsNoBot_one) m' m hK hm

/-- The initial operator of the runtimes, in the decompressed basis, has no empty cell. -/
theorem noBot_init (m₀ : Finset S × M) {A : Type} [Fintype A] [DecidableEq A]
    (ρ : Matrix A A ℂ) :
    QuerySupportedOn (fun m : A × HwReg X Z (Finset S × M) ↦ m.2) {s | NoBot s}
      (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ compressReg X Z (Finset S × M))
        (ρ ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix)) := by
  have h0 : QuerySupportedOn (fun m : A × HwReg X Z (Finset S × M) ↦ m.2)
      {((Database.empty, Database.empty, Database.empty), hwEmpty X Z, m₀)}
      (ρ ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) := by
    intro m m' hm
    change (ρ ⊗ₖ (SubState.basis (((Database.empty, Database.empty, Database.empty),
      hwEmpty X Z, m₀) : HwReg X Z (Finset S × M))).matrix) m m' ≠ 0 at hm
    rw [SubState.matrix_basis, kroneckerMap_apply] at hm
    have h := right_ne_zero_of_mul hm
    rw [Matrix.single_apply] at h
    split_ifs at h with he
    · exact ⟨he.1.symm, he.2.symm⟩
    · exact absurd rfl h
  refine QuerySupportedOn.conj h0 fun m' m hK hm ↦ ?_
  have hK' := (one_kronecker_ne_zero (a := m.1) (a' := m'.1) (b := m.2) (b' := m'.2) hK).2
  rw [Set.mem_singleton_iff] at hm
  rw [hm, compressReg, kroneckerMap_apply, compressDbs, kroneckerMap_apply,
    kroneckerMap_apply] at hK'
  have hall : ∀ {A Y : Type} [Fintype A] [DecidableEq A] [Fintype Y] [DecidableEq Y]
      (D : Database A Y), compressAll A Y D Database.empty ≠ 0 → ∀ a, (D a).isSome := by
    intro A Y _ _ _ _ D hD a
    rw [compressAll_apply_empty] at hD
    split_ifs at hD with h
    · exact Option.isSome_iff_ne_none.mpr (h a)
    · exact absurd rfl hD
  have h₁ := left_ne_zero_of_mul hK'
  exact ⟨hall _ (left_ne_zero_of_mul h₁), hall _ (left_ne_zero_of_mul (right_ne_zero_of_mul h₁)),
    hall _ (right_ne_zero_of_mul (right_ne_zero_of_mul h₁))⟩

/-- **No empty decompressed cell**: on every branch of every run of runtime 2 with record ports
from `ρ ⊗ init`, the state in the decompressed basis is supported on registers whose databases
have no empty cell. Sponge ports and reads keep the decompressed databases; a program call resets
its cell to the compressed `⊥`, the uniform superposition of the values; a record call keeps
them. -/
theorem noBot_runtimeR (m₀ : Finset S × M) {L : LocalSig.{0, 0}} (I : L.Interp)
    {W : QReg → Type} {A : QReg} (x : QuantumComp L (recHwSpec X Z S M) W A)
    (ρ : Matrix A A ℂ) (p : Σ u, W u) :
    QuerySupportedOn (fun m : p.1 × HwReg X Z (Finset S × M) ↦ m.2) {s | NoBot s}
      (MatrixMap.conj ((1 : Matrix p.1 p.1 ℂ) ⊗ₖ compressReg X Z (Finset S × M))
        (((runtimeR m₀).run I x).branch p (ρ ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix))) := by
  have h := querySupportedOn_run (decR m₀) {s | NoBot s} (decR_step_noBot m₀) I x
    (noBot_init m₀ ρ) p
  rw [run_conjReg (runtimeRH m₀) (compressReg X Z (Finset S × M)) compressReg_mul_self
    conjTranspose_compressReg I x p] at h
  exact h

end noBot

/-! ## Reads recorded: the decompressed reads against the compressed databases -/

section sandwich

open OracleSpec

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]

/-- `NoBotDb`, decided cell by cell. -/
instance noBotDbDec : DecidablePred (NoBotDb (X := X) (Z := Z)) :=
  fun D ↦ inferInstanceAs (Decidable ((∀ z, (D.1 z).isSome) ∧ (∀ x, (D.2.1 x).isSome) ∧
    ∀ x, (D.2.2 x).isSome))

/-- The compressed databases whose view through the hardwired cells `W` holds the log. -/
noncomputable def agreeDiag (W : Hw X Z) (log : QueryLog (spongeOSpec X Z)) :
    Matrix (DbReg X Z) (DbReg X Z) ℂ :=
  diagonal fun D ↦ if DbReg.Agrees log (hwView W D) then 1 else 0

/-- The databases with no empty cell whose view through `W` holds the log. -/
noncomputable def goodDiag (W : Hw X Z) (log : QueryLog (spongeOSpec X Z)) :
    Matrix (DbReg X Z) (DbReg X Z) ℂ :=
  diagonal fun D ↦ if NoBotDb D ∧ DbReg.Agrees log (hwView W D) then 1 else 0

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
theorem noBotDb_iff (D : DbReg X Z) : NoBotDb D ↔ ∃ t, ofFunDbs t = D := by
  constructor
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨(fun z ↦ (D.1 z).get (h₁ z), fun x ↦ (D.2.1 x).get (h₂ x),
      fun x ↦ (D.2.2 x).get (h₃ x)), ?_⟩
    refine Prod.ext (funext fun z ↦ ?_) (Prod.ext (funext fun x ↦ ?_) (funext fun x ↦ ?_)) <;>
      simp [ofFunDbs, Database.ofFun]
  · rintro ⟨t, rfl⟩
    simp [NoBotDb, ofFunDbs, Database.ofFun]

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
theorem dbAns_ofFunDbs (t : (Z → X) × (X → Z) × (X → Z)) (q : SpongeQuery X Z) :
    dbAns (ofFunDbs t) q = some (spongeAns t q) := by
  cases q <;> rfl

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] in
theorem agrees_hwView_ofFunDbs (W : Hw X Z) (t : (Z → X) × (X → Z) × (X → Z))
    (log : QueryLog (spongeOSpec X Z)) :
    DbReg.Agrees log (hwView W (ofFunDbs t)) ↔
      ∀ e ∈ log, spongeAns (overwrite W t) e.1 = e.2 := by
  refine forall₂_congr fun e _ ↦ ?_
  rw [dbAns_hwView, dbAns_ofFunDbs, spongeAns_overwrite]
  rcases dbAns W e.1 with _ | v <;> simp

/-- The tabulated functions consistent with the log, as databases. -/
theorem basis_mul_logProjector_mul_basis (W : Hw X Z) (log : QueryLog (spongeOSpec X Z)) :
    basisMatrix (ofFunDbs (X := X) (Z := Z)) *
        logProjector (fun t ↦ spongeAns (overwrite W t)) log *
        (basisMatrix (ofFunDbs (X := X) (Z := Z)))ᴴ = goodDiag W log := by
  ext D' D
  rw [Matrix.mul_apply]
  simp only [logProjector, Matrix.mul_diagonal, conjTranspose_apply, basisMatrix_apply]
  rw [goodDiag, diagonal_apply]
  by_cases hD : ∃ t, ofFunDbs t = D
  · obtain ⟨t0, rfl⟩ := hD
    rw [Finset.sum_eq_single t0 (fun t _ ht ↦ by
      simp [show ¬ ofFunDbs t0 = ofFunDbs t from fun h ↦ ht (ofFunDbs_injective h).symm])
      (by simp)]
    have hnb : NoBotDb (ofFunDbs t0) := (noBotDb_iff _).2 ⟨t0, rfl⟩
    have hiff := agrees_hwView_ofFunDbs W t0 log
    by_cases h' : D' = ofFunDbs t0
    · subst h'
      by_cases hc : ∀ e ∈ log, spongeAns (overwrite W t0) e.1 = e.2
      · simp only [hnb, hiff.2 hc, and_self, ↓reduceIte]
        simpa using fun x y h ↦ hc ⟨x, y⟩ h
      · have hc' : ¬ DbReg.Agrees log (hwView W (ofFunDbs t0)) := fun h ↦ hc (hiff.1 h)
        simp [hc, hc']
    · simp [h']
  · have hnb : ¬ NoBotDb D := fun h ↦ hD ((noBotDb_iff D).1 h)
    rw [Finset.sum_eq_zero fun t _ ↦ by
      simp [show ¬ D = ofFunDbs t from fun h ↦ hD ⟨t, h.symm⟩]]
    split_ifs with h1 h2
    · exact absurd (h1 ▸ h2.1) hnb
    · rfl
    · rfl

variable [Nonempty X] [Nonempty Z]

/-- **The sandwich identity in the decompressed database basis**: on the databases with no empty
cell whose view holds the log, the compressed projector of the log is the consistency scalar of
its free entries (`hw_sandwich`). -/
theorem goodDiag_mul_agreeDiag_mul_goodDiag (W : Hw X Z) (log : QueryLog (spongeOSpec X Z)) :
    goodDiag W log * (compressDbs X Z * agreeDiag W log * compressDbs X Z) * goodDiag W log =
      (spongeScalar X Z (freeLog W log) : ℂ) • goodDiag W log := by
  have h := hw_sandwich W log
  rw [conjTranspose_mul, conjTranspose_compressDbs] at h
  rw [← basis_mul_logProjector_mul_basis]
  set B := basisMatrix (ofFunDbs (X := X) (Z := Z))
  set Lt := logProjector (fun t ↦ spongeAns (overwrite W t)) log
  calc B * Lt * Bᴴ * (compressDbs X Z * agreeDiag W log * compressDbs X Z) * (B * Lt * Bᴴ)
      = B * (Lt * (Bᴴ * compressDbs X Z) * agreeDiag W log * (compressDbs X Z * B) * Lt) * Bᴴ := by
        simp only [Matrix.mul_assoc]
    _ = B * ((spongeScalar X Z (freeLog W log) : ℂ) • Lt) * Bᴴ := by rw [← h]; rfl
    _ = (spongeScalar X Z (freeLog W log) : ℂ) • (B * Lt * Bᴴ) := by
        rw [Matrix.mul_smul, Matrix.smul_mul]

variable {M' : Type} [Fintype M'] [DecidableEq M']

/-- The compressed registers whose databases, viewed through their hardwired cells, hold the
log. -/
noncomputable def agreeReg (log : QueryLog (spongeOSpec X Z)) :
    Matrix (HwReg X Z M') (HwReg X Z M') ℂ :=
  diagonal fun s ↦ if DbReg.Agrees log (hwView s.2.1 s.1) then 1 else 0

/-- The registers with no empty database cell whose view holds the log. -/
noncomputable def goodReg (log : QueryLog (spongeOSpec X Z)) :
    Matrix (HwReg X Z M') (HwReg X Z M') ℂ :=
  diagonal fun s ↦ if NoBotDb s.1 ∧ DbReg.Agrees log (hwView s.2.1 s.1) then 1 else 0

omit [Nonempty X] [Nonempty Z] [Fintype M'] in
theorem compressReg_eq_blockDiagonal :
    compressReg X Z M' = blockDiagonal fun _ : Hw X Z × M' ↦ compressDbs X Z := by
  ext ⟨D', b'⟩ ⟨D, b⟩
  simp only [compressReg, kroneckerMap_apply, blockDiagonal_apply, Matrix.one_apply]
  split_ifs <;> simp

omit [Nonempty X] [Nonempty Z] [Fintype M'] in
theorem diagonal_eq_blockDiagonal (f : HwReg X Z M' → ℂ) :
    (diagonal f : Matrix (HwReg X Z M') (HwReg X Z M') ℂ) =
      blockDiagonal fun b ↦ diagonal fun D ↦ f (D, b) := by
  ext ⟨D', b'⟩ ⟨D, b⟩
  simp only [diagonal_apply, blockDiagonal_apply, Prod.mk.injEq]
  by_cases hb : b' = b
  · subst hb
    by_cases hD : D' = D <;> simp [hD]
  · simp [hb]

/-- **The sandwich identity on the register**, block by block of the classical part. -/
theorem goodReg_mul_agreeReg_mul_goodReg (log : QueryLog (spongeOSpec X Z)) :
    goodReg (M' := M') log * (compressReg X Z M' * agreeReg log * compressReg X Z M') *
        goodReg log =
      diagonal fun s : HwReg X Z M' ↦ (spongeScalar X Z (freeLog s.2.1 log) : ℂ) *
        if NoBotDb s.1 ∧ DbReg.Agrees log (hwView s.2.1 s.1) then 1 else 0 := by
  rw [goodReg, agreeReg, diagonal_eq_blockDiagonal, diagonal_eq_blockDiagonal,
    compressReg_eq_blockDiagonal]
  simp only [← blockDiagonal_mul]
  rw [diagonal_eq_blockDiagonal]
  congr 1
  funext b
  have h := goodDiag_mul_agreeDiag_mul_goodDiag b.1 log
  rw [goodDiag, agreeDiag] at h
  rw [h, ← diagonal_smul]
  rfl

/-- **Reads are recorded, up to the read error.** A state of the program register `A` and the
hardwired register whose decompressed form is supported on databases with no empty cell whose view
through the hardwired cells holds the log (the state after decompressed reads that returned the
log) has, in the compressed basis, weight at least `1 - readError` on the databases whose view
holds the log. -/
theorem readsRecorded [AddCommGroup X] [AddCommGroup Z] {A : Type} [Fintype A] [DecidableEq A]
    (log : QueryLog (spongeOSpec X Z))
    {lh lk lk' : ℕ} (hh : readCount .h log ≤ lh) (hk : readCount .k log ≤ lk)
    (hk' : readCount .k' log ≤ lk') {σ : Matrix (A × HwReg X Z M') (A × HwReg X Z M') ℂ}
    (hσ : σ.PosSemidef)
    (hsupp : QuerySupportedOn (fun x : A × HwReg X Z M' ↦ x.2)
      {s | NoBotDb s.1 ∧ DbReg.Agrees log (hwView s.2.1 s.1)}
      (MatrixMap.conj ((1 : Matrix A A ℂ) ⊗ₖ compressReg X Z M') σ)) :
    (1 - readError X Z lh lk lk') * σ.trace.re ≤
      (((1 : Matrix A A ℂ) ⊗ₖ agreeReg log) * σ).trace.re := by
  set C1 := (1 : Matrix A A ℂ) ⊗ₖ compressReg X Z M' with hC1
  have hC : C1ᴴ = C1 := by
    rw [hC1, conjTranspose_kronecker, conjTranspose_one, conjTranspose_compressReg]
  have hCC : C1 * C1 = 1 := by
    rw [hC1, ← mul_kronecker_mul, Matrix.one_mul, compressReg_mul_self, one_kronecker_one]
  set τ := MatrixMap.conj C1 σ with hτdef
  have hτ' : τ = C1 * σ * C1 := by rw [hτdef, MatrixMap.conj_apply, hC]
  have hτpsd : τ.PosSemidef := by
    rw [hτdef, MatrixMap.conj_apply]
    exact hσ.mul_mul_conjTranspose_same C1
  set g : A × HwReg X Z M' → ℂ := fun x ↦
    if NoBotDb x.2.1 ∧ DbReg.Agrees log (hwView x.2.2.1 x.2.1) then 1 else 0 with hg
  have hG1 : (1 : Matrix A A ℂ) ⊗ₖ goodReg log = diagonal g := by
    rw [goodReg, ← diagonal_one, diagonal_kronecker_diagonal]
    simp only [one_mul, hg]
  have hτG : diagonal g * τ * diagonal g = τ := by
    ext x y
    rw [mul_diagonal, diagonal_mul]
    by_cases h : τ x y = 0
    · simp [h]
    · obtain ⟨hx, hy⟩ := hsupp x y h
      simp only [Set.mem_ofPred_eq] at hx hy
      simp [hg, hx, hy]
  have hQ : (((1 : Matrix A A ℂ) ⊗ₖ agreeReg log) * σ).trace =
      (((1 : Matrix A A ℂ) ⊗ₖ (compressReg X Z M' * agreeReg log * compressReg X Z M')) *
        τ).trace := by
    have hN : (1 : Matrix A A ℂ) ⊗ₖ (compressReg X Z M' * agreeReg log * compressReg X Z M') =
        C1 * ((1 : Matrix A A ℂ) ⊗ₖ agreeReg log) * C1 := by
      rw [hC1, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul]
    rw [hN, hτ']
    calc (((1 : Matrix A A ℂ) ⊗ₖ agreeReg log) * σ).trace
        = (((1 : Matrix A A ℂ) ⊗ₖ agreeReg log) * σ * (C1 * C1)).trace := by
          rw [hCC, Matrix.mul_one]
      _ = (C1 * (((1 : Matrix A A ℂ) ⊗ₖ agreeReg log) * σ * C1)).trace := by
          rw [Matrix.trace_mul_comm C1, Matrix.mul_assoc _ C1 C1]
      _ = (C1 * ((1 : Matrix A A ℂ) ⊗ₖ agreeReg log) * C1 * (C1 * σ * C1)).trace := by
          congr 1
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc C1 C1, hCC, Matrix.one_mul]
  set e : HwReg X Z M' → ℂ := fun s ↦ (spongeScalar X Z (freeLog s.2.1 log) : ℂ) *
    if NoBotDb s.1 ∧ DbReg.Agrees log (hwView s.2.1 s.1) then 1 else 0 with he
  have hE : (((1 : Matrix A A ℂ) ⊗ₖ (compressReg X Z M' * agreeReg log * compressReg X Z M')) *
      τ).trace = (diagonal (fun x : A × HwReg X Z M' ↦ e x.2) * τ).trace := by
    conv_lhs => rw [← hτG]
    have hD : diagonal g * ((1 : Matrix A A ℂ) ⊗ₖ
        (compressReg X Z M' * agreeReg log * compressReg X Z M')) * diagonal g =
        diagonal fun x : A × HwReg X Z M' ↦ e x.2 := by
      rw [← hG1, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.one_mul,
        goodReg_mul_agreeReg_mul_goodReg, ← diagonal_one, diagonal_kronecker_diagonal]
      simp only [one_mul, he]
    rw [← hD]
    set N := (1 : Matrix A A ℂ) ⊗ₖ (compressReg X Z M' * agreeReg log * compressReg X Z M')
    set Dg := diagonal g
    rw [show N * (Dg * τ * Dg) = (N * Dg * τ) * Dg by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have htr : σ.trace = τ.trace := by
    rw [hτ', Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hCC, Matrix.mul_one]
  rw [hQ, hE, htr]
  simp only [Matrix.trace, diag_apply, diagonal_mul, Complex.re_sum]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ ↦ ?_
  have hnn : 0 ≤ (τ x x).re := by
    have := Complex.le_def.mp (hτpsd.diag_nonneg (i := x))
    simpa using this.1
  by_cases h0 : τ x x = 0
  · simp [h0]
  · obtain ⟨hx, -⟩ := hsupp x x h0
    simp only [Set.mem_ofPred_eq] at hx
    have hs := one_sub_readError_le_spongeScalar
      ((readCount_freeLog_le x.2.2.1 .h log).trans hh)
      ((readCount_freeLog_le x.2.2.1 .k log).trans hk)
      ((readCount_freeLog_le x.2.2.1 .k' log).trans hk')
    simp only [he, hx, and_self, ↓reduceIte, mul_one, Complex.re_ofReal_mul]
    exact mul_le_mul_of_nonneg_right hs hnn

end sandwich



/-! ## The win weight against the event weight, from a decomposition of the winning runs -/

section reduction

variable {X Z : Type} [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z]
  [AddCommGroup X] [AddCommGroup Z] [Nonempty X] [Nonempty Z]
  {S : Type} [Fintype S] [DecidableEq S] {M : Type} [Fintype M] [DecidableEq M]

/-- The win bit of a Boolean leaf. -/
def winBit (p : Σ u, QuantumComp₂.Leaf (QReg.of Unit) Bool u) : Bool := p.2.2

omit [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] [AddCommGroup X] [AddCommGroup Z]
  [Nonempty X] [Nonempty Z] [Fintype S] [Fintype M] [DecidableEq M] in
theorem readError_nonneg (lh lk lk' : ℕ) [Fintype X] [Fintype Z] :
    0 ≤ readError X Z lh lk lk' := by
  unfold readError
  positivity

/-- **The winning runs, decomposed along the final reads.** The win weight of `x` in `runtimeR m₀`
is covered by operators `σ i` (one per run of the final reads, with its log `log i`), each of
which, in the decompressed basis, has no empty cell and its view holds the log (the reads were
decompressed-basis measurements returning the log), and, in the compressed basis, is supported
on registers where a view holding the log is in `Bad`; their event weights are part of the event
weight of the run. -/
structure WinDecomp (m₀ : Finset S × M)
    (x : QComp (recHwSpec X Z S M) (QReg.of Unit) (QReg.of Unit) Bool)
    (Bad : Set (HwReg X Z (Finset S × M))) [DecidablePred (· ∈ Bad)] (lh lk lk' : ℕ) where
  /-- The runs of the final reads. -/
  ι : Type
  /-- The operator of a run. -/
  σ : ι → Matrix (Unit × HwReg X Z (Finset S × M)) (Unit × HwReg X Z (Finset S × M)) ℂ
  /-- The log of a run's reads. -/
  log : ι → QueryLog (spongeOSpec X Z)
  psd : ∀ i, (σ i).PosSemidef
  countH : ∀ i, readCount .h (log i) ≤ lh
  countK : ∀ i, readCount .k (log i) ≤ lk
  countK' : ∀ i, readCount .k' (log i) ≤ lk'
  /-- In the decompressed basis: no empty cell, and the view holds the log. -/
  recorded : ∀ i, QuerySupportedOn (fun y : Unit × HwReg X Z (Finset S × M) ↦ y.2)
    {s | NoBotDb s.1 ∧ DbReg.Agrees (log i) (hwView s.2.1 s.1)}
    (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ compressReg X Z (Finset S × M)) (σ i))
  /-- In the compressed basis: a view holding the log is in the event. -/
  bad : ∀ i, QuerySupportedOn (fun y : Unit × HwReg X Z (Finset S × M) ↦ y.2)
    {s | DbReg.Agrees (log i) (hwView s.2.1 s.1) → s ∈ Bad} (σ i)
  win : (runtimeR m₀).evalDistMap .instruments x (SubState.basis ()) winBit {true} ≤
    ∑' i, ENNReal.ofReal (σ i).trace.re
  event : ∑' i, ENNReal.ofReal
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector Bad) (σ i)).trace.re ≤
    (runtimeR m₀).eventWeight .instruments (hwProjector Bad) x
      ((SubState.basis ()).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix)
  mass : ∑' i, ENNReal.ofReal (σ i).trace.re ≤ 1

omit [Fintype S] [DecidableEq S] [Fintype M] [DecidableEq M] [AddCommGroup X] [AddCommGroup Z]
  [Nonempty X] [Nonempty Z] in
/-- On an operator supported where the log's view lies in the event, the weight of the log's view
is at most the weight of the event. -/
theorem trace_agree_le_trace_bad {M' : Type} [Fintype M'] [DecidableEq M']
    (Bad : Set (HwReg X Z M')) [DecidablePred (· ∈ Bad)] (log : QueryLog (spongeOSpec X Z))
    {σ : Matrix (Unit × HwReg X Z M') (Unit × HwReg X Z M') ℂ} (hσ : σ.PosSemidef)
    (hb : QuerySupportedOn (fun y : Unit × HwReg X Z M' ↦ y.2)
      {s | DbReg.Agrees log (hwView s.2.1 s.1) → s ∈ Bad} σ) :
    (((1 : Matrix Unit Unit ℂ) ⊗ₖ agreeReg log) * σ).trace.re ≤
      (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector Bad) σ).trace.re := by
  have hP : ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector Bad)ᴴ *
      ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector Bad) =
      diagonal fun y : Unit × HwReg X Z M' ↦ if y.2 ∈ Bad then 1 else 0 := by
    rw [conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.one_mul,
      hwProjector, labelProjector, diagonal_conjTranspose, diagonal_mul_diagonal, ← diagonal_one,
      diagonal_kronecker_diagonal]
    congr 1
    funext y
    by_cases h : y.2 ∈ Bad <;> simp [h]
  have hA : (1 : Matrix Unit Unit ℂ) ⊗ₖ agreeReg log =
      diagonal fun y : Unit × HwReg X Z M' ↦
        if DbReg.Agrees log (hwView y.2.2.1 y.2.1) then 1 else 0 := by
    rw [agreeReg, ← diagonal_one, diagonal_kronecker_diagonal]
    simp only [one_mul]
  rw [MatrixMap.trace_conj_apply, hP, hA]
  simp only [Matrix.trace, diag_apply, diagonal_mul, Complex.re_sum]
  refine Finset.sum_le_sum fun y _ ↦ ?_
  have hnn : 0 ≤ (σ y y).re := by
    have := Complex.le_def.mp (hσ.diag_nonneg (i := y))
    simpa using this.1
  by_cases h0 : σ y y = 0
  · simp [h0]
  · have hy := (hb y y h0).1
    by_cases ha : DbReg.Agrees log (hwView y.2.2.1 y.2.1)
    · simp [ha, hy ha]
    · by_cases hB : y.2 ∈ Bad <;> simp [ha, hB, hnn]

/-- **The win weight is at most the event weight plus the read error**, given a decomposition of
the winning runs along the final reads. -/
theorem win_le_of_winDecomp {m₀ : Finset S × M}
    {x : QComp (recHwSpec X Z S M) (QReg.of Unit) (QReg.of Unit) Bool}
    {Bad : Set (HwReg X Z (Finset S × M))} [DecidablePred (· ∈ Bad)] {lh lk lk' : ℕ}
    (d : WinDecomp m₀ x Bad lh lk lk') :
    (runtimeR m₀).evalDistMap .instruments x (SubState.basis ()) winBit {true} ≤
      (runtimeR m₀).eventWeight .instruments (hwProjector Bad) x
          ((SubState.basis ()).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) +
        ENNReal.ofReal (readError X Z lh lk lk') := by
  set err := readError X Z lh lk lk'
  have herr : 0 ≤ err := readError_nonneg lh lk lk'
  have hi : ∀ i, ENNReal.ofReal (d.σ i).trace.re ≤
      ENNReal.ofReal (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector Bad)
        (d.σ i)).trace.re + ENNReal.ofReal err * ENNReal.ofReal (d.σ i).trace.re := by
    intro i
    have h1 := readsRecorded (log := d.log i) (d.countH i) (d.countK i) (d.countK' i) (d.psd i)
      (d.recorded i)
    have h2 := trace_agree_le_trace_bad Bad (d.log i) (d.psd i) (d.bad i)
    rw [← ENNReal.ofReal_mul herr]
    refine (ENNReal.ofReal_le_ofReal ?_).trans ENNReal.ofReal_add_le
    linarith
  calc (runtimeR m₀).evalDistMap .instruments x (SubState.basis ()) winBit {true}
      ≤ ∑' i, ENNReal.ofReal (d.σ i).trace.re := d.win
    _ ≤ ∑' i, (ENNReal.ofReal (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector Bad)
          (d.σ i)).trace.re + ENNReal.ofReal err * ENNReal.ofReal (d.σ i).trace.re) :=
        ENNReal.tsum_le_tsum hi
    _ = ∑' i, ENNReal.ofReal (MatrixMap.conj ((1 : Matrix Unit Unit ℂ) ⊗ₖ hwProjector Bad)
          (d.σ i)).trace.re + ENNReal.ofReal err * ∑' i, ENNReal.ofReal (d.σ i).trace.re := by
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_left]
    _ ≤ _ := by
        gcongr
        · exact d.event
        · exact (mul_le_mul_right d.mass _).trans_eq (mul_one _)

end reduction


/-! ## The restated `endReads` -/

section endReads

variable {S : Type} [Fintype S] [DecidableEq S] [DecidableEq Selections]

/-- **`endReads` from a decomposition of the winning runs** (Security's debt, restated for any
label type `S` and program `x`): the win weight in `runtimeR m₀` is at most the event weight of
`BadRS L progCap` plus the read error of the verification's `verifyBlocks` reads of each function,
given a `WinDecomp`. The `bad` field of the decomposition follows from `bad_of_winFacts`. -/
theorem endReads_of_winDecomp (L : HonestTable) (m₀ : Finset S × Selections)
    (x : QComp (recHwSpec X Z S Selections) (QReg.of Unit) (QReg.of Unit) Bool)
    [DecidablePred (· ∈ BadRS (S := S) L progCap)]
    (d : WinDecomp m₀ x (BadRS L progCap) verifyBlocks verifyBlocks verifyBlocks) :
    (runtimeR m₀).evalDistMap .instruments x (SubState.basis ()) winBit {true} ≤
      (runtimeR m₀).eventWeight .instruments (hwProjector (BadRS L progCap)) x
          ((SubState.basis ()).matrix ⊗ₖ (runtimeR (X := X) (Z := Z) m₀).init.matrix) +
        ENNReal.ofReal (readError X Z verifyBlocks verifyBlocks verifyBlocks) :=
  win_le_of_winDecomp d

end endReads

end Quantum.Xmss.Assembly

end
