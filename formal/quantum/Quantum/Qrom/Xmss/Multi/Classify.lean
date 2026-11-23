module

public import Quantum.Qrom.Xmss.Multi.Events
public import Quantum.Qrom.Xmss.Classify

@[expose] public section

/-!
# leanXMSS for `n` users in the random-oracle model: a win is in the event

`win_imp_badQ_prefix` strengthens the single-user `win_imp_badQ`: the witness cell is hashed under
the key's public parameter. The event `BadQP hon P` is `BadQ hon` restricted to the cells of prefix
`P` (`badQ_of_badQP`); the proof is the single-user one, every witness being a verification read
or an honest cell of the key, both cells `cell v.param s d` of a prefixed slot (`prefixOf_cell`).

`win_imp_badQN`: a forgery for user `i` that verifies against `i`'s public key, with the
single-user hypotheses for `i` on the projection `projU i s` (the register with `i`'s memory; same
union view, `unionH_projU`), puts the state in `BadQN` when the public parameters are distinct: the
witness is owned by `i` (`ownerOf_eq_some`), where `BadQN` targets are `i`'s single-user targets
(`mem_badQN_of_badQP`). Other users' hardwired cells have other prefixes and play no role.
-/

open Quantum Quantum.Sponge OracleComp OracleSpec
open HashSig HashSig.OverPermutation LeanXmss
open Quantum.Xmss (Slot Known sibling last_divergence evalWithAnswerFn_sequenceFin
  queriesSatisfy_bind_iff eq_topLayer signature_eq_layers)
open Quantum.SufCma (QueriesSatisfy)
open Quantum.Qrom.MultiUser (ownerOf ownerOf_eq_some)

namespace Quantum.Qrom.Xmss.Multi

local notation "ev" H => evalWithAnswerFn (romAnswers H)

/-! ## The single-user event on the cells of one prefix -/

/-- **The XMSS targets on the cells of prefix `P`.** -/
def xmssTgtQP (hon : HonestCells) (P : PublicParameter) (W : Hw HashOutput HashDomain)
    (m : SelMem) (x : HashDomain) : Set HashOutput :=
  {y | prefixOf x = some P ∧ tgtDigest hon W.1 m x = some (truncateHash y)}

/-- **The single-user XMSS event on the cells of prefix `P`.** -/
abbrev BadQP (hon : HonestCells) (P : PublicParameter) :
    Set (RomReg HashDomain HashOutput SelMem) :=
  CellTargetBad (xmssTgtQP hon P)

section Hits

variable {hon : HonestCells} {P : PublicParameter} {s : RomReg HashDomain HashOutput SelMem}

theorem mem_xmssTgtQP {W : Hw HashOutput HashDomain} {m : SelMem} {x : HashDomain}
    {y : HashOutput} :
    y ∈ xmssTgtQP hon P W m x ↔
      prefixOf x = some P ∧ tgtDigest hon W.1 m x = some (truncateHash y) :=
  Iff.rfl

theorem badQ_of_badQP (h : s ∈ BadQP hon P) : s ∈ BadQ hon := by
  obtain ⟨x, y, hxy, hy⟩ := h
  exact mem_badQ_iff.2 ⟨x, y, hxy, (mem_xmssTgtQP.1 hy).2⟩

/-- **A Struct hit of prefix `P`.** -/
theorem mem_badQP_of_struct {x c : HashDomain} {sl : Slot} {d : Digest}
    (hx : (unionH s x).isSome) (hpre : prefixOf x = some P) (hsl : slotOf x = some sl)
    (hmsg : ∀ l e, sl ≠ .msg l e) (hc : hon sl = some (c, d))
    (hd : truncateHash (viewH (unionH s) x) = d) (hne : ¬(c = x ∧ (s.2.1.1 x).isSome)) :
    s ∈ BadQP hon P := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hx
  refine ⟨x, y, hy, mem_xmssTgtQP.2 ⟨hpre, ?_⟩⟩
  rw [tgtDigest, hsl, Option.bind_some, slotDigest_of_ne_msg _ _ _ hmsg, structDigest, hc,
    Option.bind_some, ite_eq_right hne, ← hd, viewH, hy]
  rfl

/-- **An Enc hit of prefix `P`.** -/
theorem mem_badQP_of_enc {x c : HashDomain} {l : Layer} {e : KeyIndex} {d : Digest}
    (hx : (unionH s x).isSome) (hpre : prefixOf x = some P) (hsl : slotOf x = some (.msg l e))
    (hm : s.2.2 l e = some (c, d)) (hne : c ≠ x) (hd : truncateHash (viewH (unionH s) x) = d) :
    s ∈ BadQP hon P := by
  obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 hx
  refine ⟨x, y, hy, mem_xmssTgtQP.2 ⟨hpre, ?_⟩⟩
  rw [tgtDigest, hsl, Option.bind_some, slotDigest_msg, hm, Option.bind_some, ite_eq_right hne,
    ← hd, viewH, hy]
  rfl

end Hits

/-! ## Walks meeting the honest table -/

section Meet

variable {S0 : MasterSeed} {v : QTable} {s : RomReg HashDomain HashOutput SelMem}

/-- **A chain walk ending at the honest chain** (no hit of prefix `v.param`): it starts at the
honest value, and the honest cell of its first step is hardwired. -/
theorem chain_meetP (hnb : s ∉ BadQP (QTable.honCell S0 v) v.param) {l : Layer} {e : KeyIndex}
    {i : ChainIndex} {a n : ℕ} (hn : 0 < n) (han : a + n ≤ chainLength - 1) {w : Digest}
    (hQ : QueriesSatisfy (romAnswers (viewH (unionH s))) (ReadBy (unionH s))
      (Over.chainWalk hashQ v.param l e i a n w))
    (hend : (ev (viewH (unionH s))) (Over.chainWalk hashQ v.param l e i a n w) =
      v.chainValue l e i (a + n)) :
    w = v.chainValue l e i a ∧
      ∀ h : a < chainLength - 1, (s.2.1.1 (cellOf S0 (.chain l e i ⟨a, h⟩) v)).isSome := by
  let H := viewH (unionH s)
  let f : ℕ → Digest := fun k ↦ (ev H) (Over.chainWalk hashQ v.param l e i a k w)
  let g : ℕ → Digest := fun k ↦ v.chainValue l e i (a + k)
  let u : ℕ → HashDomain := fun k ↦ chainCell v.param l e i (a + k) (f k)
  let u' : ℕ → HashDomain := fun k ↦ chainCell v.param l e i (a + k) (g k)
  have hit : ∀ k (hk : k < n), f (k + 1) = g (k + 1) →
      ¬(u' k = u k ∧ (s.2.1.1 (u k)).isSome) → False := by
    intro k hk hfg hne
    have hb : a + k < chainLength - 1 := by omega
    apply hnb
    refine mem_badQP_of_struct (x := u k) (sl := .chain l e ⟨a + k, hb⟩ i)
      (readBy_chainWalk hQ k hk hb) ?_ ?_ (fun _ _ h ↦ by cases h) rfl ?_ ?_
    · show prefixOf (chainCell v.param l e i (a + k) (f k)) = _
      rw [chainCell_of_lt hb]
      exact prefixOf_cell _ (by trivial) rfl _
    · show slotOf (chainCell v.param l e i (a + k) (f k)) = _
      rw [chainCell_of_lt hb]
      exact slotOf_cell _ (by trivial) _
    · exact (ev_chainWalk_succ H _ _ _ _ a k w hb).symm.trans
        (hfg.trans (truncateHash_chain v l e i hb).symm)
    · rintro ⟨h1, h2⟩
      exact hne ⟨(chainCell_honest S0 v l e i hb).trans h1, h2⟩
  have hstep : ∀ k, k + 1 < n → u (k + 1) = u' (k + 1) → f (k + 1) = g (k + 1) :=
    fun k hk h ↦ chainCell_inj (by omega) h
  rcases last_divergence u u' f g n hend hstep with ⟨k, hk, hne, hfg⟩ | hall
  · exact (hit k hk hfg fun h ↦ hne h.1.symm).elim
  · have h0 : f 0 = g 0 := chainCell_inj (by omega) (hall 0 hn)
    refine ⟨h0, fun ha ↦ ?_⟩
    by_contra hEx
    have h1 : f 1 = g 1 := by
      rcases Nat.lt_or_ge 1 n with h | h
      · exact chainCell_inj (by omega) (hall 1 h)
      · obtain rfl : n = 1 := by omega
        exact hend
    exact hit 0 hn h1 fun h ↦ hEx (by
      rw [← chainCell_honest S0 v l e i ha]
      exact (congrArg (fun x ↦ (s.2.1.1 x).isSome) h.1).trans h.2)

/-- **A Merkle path ending at the honest root** (no hit of prefix `v.param`): it starts at the
honest leaf value and its siblings are the honest authentication path. -/
theorem path_meetP (hnb : s ∉ BadQP (QTable.honCell S0 v) v.param) {l : Layer} {e : KeyIndex}
    {path : Fin layerHeight → Digest} {cur : Digest}
    (hQ : QueriesSatisfy (romAnswers (viewH (unionH s))) (ReadBy (unionH s))
      (Over.treeFold hashQ v.param l e path layerHeight cur))
    (hroot : (ev (viewH (unionH s))) (Over.treeFold hashQ v.param l e path layerHeight cur) =
      v.treeValue l layerHeight (e.val / 2 ^ layerHeight)) :
    cur = v.treeValue l 0 e.val ∧ path = v.authPath l e := by
  let H := viewH (unionH s)
  let f : ℕ → Digest := fun k ↦ (ev H) (Over.treeFold hashQ v.param l e path k cur)
  let g : ℕ → Digest := fun k ↦ v.treeValue l k (e.val / 2 ^ k)
  let hs : ℕ → Digest := fun k ↦ v.treeValue l k (e.val / 2 ^ k ^^^ 1)
  let u : ℕ → HashDomain := fun k ↦ nodeCell v.param l e (sibling path) k (f k)
  let u' : ℕ → HashDomain := fun k ↦ nodeCell v.param l e hs k (g k)
  have hstep : ∀ k, k + 1 < layerHeight → u (k + 1) = u' (k + 1) → f (k + 1) = g (k + 1) :=
    fun _ hk h ↦ (nodeCell_inj hk h).1
  rcases last_divergence u u' f g layerHeight hroot hstep with ⟨k, hk, hne, hfg⟩ | hall
  · exfalso
    apply hnb
    refine mem_badQP_of_struct (x := u k) (readBy_treeFold hQ k hk)
      (prefixOf_cell _ (addressable_node_path l e hk) rfl _)
      (slotOf_cell _ (addressable_node_path l e hk) _) (fun _ _ h ↦ by cases h)
      (honCell_node_path S0 v l e hk (index_node_path e hk)) ?_ ?_
    · exact (ev_treeFold_succ H _ _ _ _ k cur).symm.trans
        (hfg.trans (truncateHash_node v l hk (index_node_path e hk)).symm)
    · rintro ⟨h1, -⟩
      exact hne (h1.symm.trans (nodeCell_honest S0 v l e hk).symm)
  · have h0 := (nodeCell_inj (by decide) (hall 0 (by decide))).1
    change cur = v.treeValue l 0 (e.val / 2 ^ 0) at h0
    rw [pow_zero, Nat.div_one] at h0
    refine ⟨h0, funext fun k ↦ ?_⟩
    have hk := (nodeCell_inj k.isLt (hall k.val k.isLt)).2
    simp only [sibling, k.isLt, ↓reduceDIte] at hk
    exact hk

end Meet

/-! ## Both layers -/

section Layers

variable {S0 : MasterSeed} {v : QTable} {H : HashDomain → HashOutput}
  {s : RomReg HashDomain HashOutput SelMem} {log : QueryLog SigningOracleSpec}

/-- **A layer reaching the honest root of its tree** (no hit of prefix `v.param`) is the
signature of that layer by a signed request with the same key, on the same message. -/
theorem layer_meetP (hM : ∀ r ∈ log, Records v H s.2.2 r.1)
    (hEx : HwKnown S0 v H s (log.map Sigma.fst))
    (hvalid : SigningTranscript.NoLeafIndexReused log)
    (hnb : s ∉ BadQP (QTable.honCell S0 v) v.param)
    {l : Layer} {e : KeyIndex} {msg : MsgBytes} {part : LayerSignature}
    (hQ : QueriesSatisfy (romAnswers (viewH (unionH s))) (ReadBy (unionH s))
      (Over.layerRoot hashQ v.param l e msg.1 part))
    (hr : (ev (viewH (unionH s))) (Over.layerRoot hashQ v.param l e msg.1 part) =
      some (v.treeValue l layerHeight (e.val / 2 ^ layerHeight))) :
    ∃ r ∈ log, keyIndexOnLayer r.1.leafIndex l = e ∧ msg = layerMsg v r.1 l ∧
      v.layerSignature H l e msg (layerBase v r.1 l) = some part := by
  obtain ⟨x, E, hx, hQm, hQc, hEeq, hQl, hQt, hroot⟩ := layerRoot_spec hQ hr
  obtain ⟨hleaf, hpath⟩ := path_meetP hnb hQt hroot
  -- The leaf: the forged chain ends are the honest ones.
  have hE : E = v.endpoints l e := by
    by_contra hne
    apply hnb
    refine mem_badQP_of_struct hQl (prefixOf_cell _ (by trivial) rfl _)
      (slotOf_cell _ (by trivial) _) (fun _ _ h ↦ by cases h)
      (rfl : QTable.honCell S0 v (.leaf l e) =
        some (cellOf S0 (.leaf l e) v, truncateHash (v (.leaf l e))))
      (hleaf.trans (truncateHash_leaf v l e).symm) ?_
    rintro ⟨hc, -⟩
    exact hne (cell_payload_inj (by trivial) hc).symm
  -- The chains: the forged values are honest, and the honest cells leaving them hardwired.
  have hchain : ∀ i, part.chainValues i = v.chainValue l e i (x i).val ∧
      ∀ h : (x i).val < chainLength - 1,
        (s.2.1.1 (cellOf S0 (.chain l e i ⟨(x i).val, h⟩) v)).isSome := by
    intro i
    have hEi : E i = v.chainValue l e i (chainLength - 1) := congrFun hE i
    rw [hEeq i] at hEi
    by_cases h3 : (x i).val < chainLength - 1
    · have hsum : (x i).val + (chainLength - 1 - (x i).val) = chainLength - 1 := by omega
      exact chain_meetP hnb (a := (x i).val) (n := chainLength - 1 - (x i).val) (by omega)
        (by omega) (hQc i) (hEi.trans (congrArg (v.chainValue l e i) hsum.symm))
    · have h3' : (x i).val = chainLength - 1 := by have := (x i).isLt; omega
      refine ⟨?_, fun h ↦ absurd h h3⟩
      have hv : (ev (viewH (unionH s))) (Over.recoverChain hashQ v.param l e i (x i)
          (part.chainValues i)) = part.chainValues i := by
        show (ev (viewH (unionH s))) (Over.chainWalk hashQ v.param l e i (x i).val
          (chainLength - 1 - (x i).val) (part.chainValues i)) = _
        rw [h3', Nat.sub_self]
        rfl
      exact hv.symm.trans (hEi.trans (congrArg (v.chainValue l e i) h3'.symm))
  -- A hardwired step is known: a signature by the same key opened its chain at or below it.
  have hknown : ∀ i (h : (x i).val < chainLength - 1),
      Known (v.disclosures H (log.map Sigma.fst)) (.chain l e i (x i).val) :=
    fun i h ↦ hEx l e i ⟨(x i).val, h⟩ ((hchain i).2 h)
  have hvx := Quantum.Xmss.Codeword.sum_eq_of_decode hx
  obtain ⟨i0, hi0⟩ := Quantum.Xmss.Codeword.exists_lt_of_sum hvx
  obtain ⟨req, hreq, hkey, sel, hsel, -⟩ := exists_signed_of_known (hknown i0 hi0)
  obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hreq
  have hle : ∀ i, sel.2 i ≤ x i := by
    intro i
    by_cases h : (x i).val < chainLength - 1
    · obtain ⟨req', hreq', hkey', sel', hsel', hj⟩ := exists_signed_of_known (hknown i h)
      obtain ⟨r', hr', rfl⟩ := List.mem_map.1 hreq'
      obtain ⟨hm1, hm2⟩ := layer_eq_of_key (v := v) hvalid hr hr' (hkey.trans hkey'.symm)
      rw [hm1, hm2, hsel'] at hsel
      obtain rfl := Option.some.inj hsel
      exact hj
    · show (sel.2 i).val ≤ (x i).val
      have := (sel.2 i).isLt
      omega
  -- Incomparability: the forged word is the selected one.
  have hvs := decode_of_select hsel
  have hxs : sel.2 = x :=
    Quantum.Xmss.Codeword.eq_of_le (Quantum.Xmss.Codeword.sum_eq_of_decode hvs) hvx hle
  -- The message-digest cell is the selected one, or an Enc hit.
  have hmeq : cell v.param (.msg l e) (msg, part.randomizer) =
      cell v.param (.msg l e) (layerMsg v r.1 l, sel.1) := by
    by_contra hne
    apply hnb
    have hMr := hM r hr l sel (by rw [hkey]; exact hsel)
    rw [hkey] at hMr
    exact mem_badQP_of_enc hQm (prefixOf_cell _ (by trivial) rfl _)
      (slotOf_cell _ (by trivial) _) hMr (Ne.symm hne)
      (Quantum.Xmss.Codeword.eq_of_decode hx (hxs ▸ hvs))
  obtain ⟨hmsgEq, hρ⟩ := Prod.mk.inj (cell_payload_inj (by trivial) hmeq)
  refine ⟨r, hr, hkey, hmsgEq, ?_⟩
  have hcv : (fun i ↦ v.chainValue l e i (sel.2 i).val) = part.chainValues :=
    funext fun i ↦ by rw [hxs]; exact (hchain i).1.symm
  rw [hmsgEq, QTable.layerSignature, hsel, Option.map_some, hcv, ← hρ, ← hpath]

/-- **A win is in the event, at a cell of the key's prefix**: `win_imp_badQ` with the witness
cell hashed under `v.param`. -/
theorem win_imp_badQ_prefix (S0 : MasterSeed) (v : QTable) (H : HashDomain → HashOutput)
    (s : RomReg HashDomain HashOutput SelMem) (log : QueryLog SigningOracleSpec)
    (forgery : Forgery) (hlog : ∀ r ∈ log, r.2 = v.signature H r.1)
    (hM : ∀ r ∈ log, Records v H s.2.2 r.1) (hEx : HwKnown S0 v H s (log.map Sigma.fst))
    (hwin : SigningTranscript.NoLeafIndexReused log ∧
      ¬Common.SufCma.SignerReturnedForgery SigningRequest.message log forgery.message
        forgery.signature)
    (hverify : (honestEval (viewH (unionH s)) (xmssRom.verify v.publicKey forgery)).1 = true)
    (hreads : ∀ c ∈ (honestEval (viewH (unionH s)) (xmssRom.verify v.publicKey forgery)).2,
      (unionH s c).isSome) :
    s ∈ BadQP (QTable.honCell S0 v) v.param := by
  by_contra hnb
  have hv : (ev (viewH (unionH s)))
      (Over.verify hashQ v.publicKey forgery.message forgery.signature) = true := hverify
  have hq : QueriesSatisfy (romAnswers (viewH (unionH s))) (ReadBy (unionH s))
      (Over.verify hashQ v.publicKey forgery.message forgery.signature) :=
    readBy_of_honestEval hreads
  set idx := forgery.signature.leafIndex
  simp only [Over.verify, evalWithAnswerFn_bind] at hv
  simp only [Over.verify] at hq
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
      -- The top layer: a signed top key's layer, on the honest bottom root.
      have hlt : (keyIndexOnLayer idx topLayer).val < 2 ^ layerHeight :=
        QTable.keyIndexOnLayer_top_lt idx
      have hdiv1 : (keyIndexOnLayer idx topLayer).val / 2 ^ layerHeight = 0 :=
        Nat.div_eq_of_lt hlt
      have hrt : (ev (viewH (unionH s))) (Over.layerRoot hashQ v.param topLayer
          (keyIndexOnLayer idx topLayer) (rootBytes R).1 (forgery.signature.layers topLayer)) =
          some (v.treeValue topLayer layerHeight
            ((keyIndexOnLayer idx topLayer).val / 2 ^ layerHeight)) := by
        rw [hdiv1]
        exact ht.trans (congrArg some hv)
      obtain ⟨r1, hr1, hkey1, hmsg1, hsig1⟩ :=
        layer_meetP (msg := rootBytes R) hM hEx hwin.1 hnb hqt hrt
      rw [layerMsg_top] at hmsg1
      have hR : R = v.bottomRoot idx := by
        have h1 : R = v.bottomRoot r1.1.leafIndex :=
          littleEndianBytes_inj (n := 16) (congrArg Subtype.val hmsg1)
        rw [h1, QTable.bottomRoot, QTable.bottomRoot, hkey1]
      -- The bottom layer: a signed request's layer, on the forged message.
      have hdiv0 : (keyIndexOnLayer idx bottomLayer).val / 2 ^ layerHeight =
          (keyIndexOnLayer idx topLayer).val := by
        simp [keyIndexOnLayer, bottomLayer, topLayer, layerHeight]
      have hrb : (ev (viewH (unionH s))) (Over.layerRoot hashQ v.param bottomLayer
          (keyIndexOnLayer idx bottomLayer) (messageBytes forgery.message).1
          (forgery.signature.layers bottomLayer)) =
          some (v.treeValue bottomLayer layerHeight
            ((keyIndexOnLayer idx bottomLayer).val / 2 ^ layerHeight)) := by
        rw [hdiv0]
        exact hb.trans (congrArg some hR)
      obtain ⟨r0, hr0, hkey0, hmsg0, hsig0⟩ :=
        layer_meetP (msg := messageBytes forgery.message) hM hEx hwin.1 hnb hqb hrb
      rw [layerMsg_bottom] at hmsg0
      have hidx : r0.1.leafIndex = idx := Fin.ext (by
        have := congrArg Fin.val hkey0
        simpa [keyIndexOnLayer, bottomLayer] using this)
      have hm : r0.1.message = forgery.message :=
        (littleEndianBytes_inj (n := 32) (congrArg Subtype.val hmsg0)).symm
      -- The forgery is the signature of that request.
      have hb0 : v.bottomSignature H r0.1 = some (forgery.signature.layers bottomLayer) := by
        rw [QTable.bottomSignature, hkey0, ← hmsg0, ← layerBase_bottom]
        exact hsig0
      have hk01 : keyIndexOnLayer r0.1.leafIndex topLayer =
          keyIndexOnLayer r1.1.leafIndex topLayer := by
        rw [hidx, hkey1]
      have hbase := (layer_eq_of_key (v := v) hwin.1 hr0 hr1 hk01).2
      rw [layerBase_top, layerBase_top] at hbase
      have ht0 : v.topSignature H r0.1 = some (forgery.signature.layers topLayer) := by
        rw [QTable.topSignature, hbase, hidx, ← hR, ← layerBase_top]
        exact hsig1
      have hsig : v.signature H r0.1 = some forgery.signature := by
        simp only [QTable.signature, hb0, ht0, Option.bind_some, Option.map_some]
        rw [hidx, signature_eq_layers]
      exact hwin.2 ⟨r0, hr0, hm, (hlog r0 hr0).trans hsig⟩
    · simp at hv
  · simp at hv

end Layers

/-! ## `n` users -/

variable {n : ℕ}

/-- **User `i`'s view of the register**: the database and hardwired cells, and `i`'s memory. -/
def projU (i : Fin n) (s : RomReg HashDomain HashOutput (SelMemN n)) :
    RomReg HashDomain HashOutput SelMem :=
  (s.1, s.2.1, s.2.2 i)

theorem unionH_projU (i : Fin n) (s : RomReg HashDomain HashOutput (SelMemN n)) :
    unionH (projU i s) = unionH s :=
  rfl

/-- **A hit of user `i`'s prefix is a hit for `n` users**, with distinct public parameters: the
witness is owned by `i`, whose single-user targets are the targets of `BadQN`. -/
theorem mem_badQN_of_badQP {hon : Fin n → HonestCells} {P : Fin n → PublicParameter}
    (hP : Function.Injective P) {s : RomReg HashDomain HashOutput (SelMemN n)} {i : Fin n}
    (h : projU i s ∈ BadQP (hon i) (P i)) : s ∈ BadQN hon P := by
  obtain ⟨x, y, hxy, hy⟩ := h
  obtain ⟨hpre, hy⟩ := mem_xmssTgtQP.1 hy
  exact mem_badQN_iff.2 ⟨x, y, hxy, (tgtDigestN_of_owner _ _ (ownerOf_eq_some hP hpre)).trans hy⟩

/-- **A win for `n` users is in the event**: a forgery for user `i` that verifies against `i`'s
public key with every hashed cell recorded or hardwired, against a valid transcript of `i`'s honest
signatures and not returned by `i`'s signer, puts the state in `BadQN`, when the public parameters
are distinct, every hardwired honest chain cell of `i` has a known input and `i`'s memory records
`i`'s selections. -/
theorem win_imp_badQN (S0 : Fin n → MasterSeed) (w : QTableN n) (hP : PDistinct w)
    (H : HashDomain → HashOutput) (s : RomReg HashDomain HashOutput (SelMemN n)) (i : Fin n)
    (log : QueryLog SigningOracleSpec) (forgery : Forgery)
    (hlog : ∀ r ∈ log, r.2 = (w.user i).signature H r.1)
    (hM : ∀ r ∈ log, Records (w.user i) H (s.2.2 i) r.1)
    (hEx : HwKnown (S0 i) (w.user i) H (projU i s) (log.map Sigma.fst))
    (hwin : SigningTranscript.NoLeafIndexReused log ∧
      ¬Common.SufCma.SignerReturnedForgery SigningRequest.message log forgery.message
        forgery.signature)
    (hverify : (honestEval (viewH (unionH s))
      (xmssRom.verify (w.user i).publicKey forgery)).1 = true)
    (hreads : ∀ c ∈ (honestEval (viewH (unionH s))
      (xmssRom.verify (w.user i).publicKey forgery)).2, (unionH s c).isSome) :
    s ∈ BadQN (honN S0 w) w.params :=
  mem_badQN_of_badQP hP (win_imp_badQ_prefix (S0 i) (w.user i) H (projU i s) log forgery hlog
    hM hEx hwin (by rw [unionH_projU]; exact hverify) (by rw [unionH_projU]; exact hreads))

end Quantum.Qrom.Xmss.Multi

end
