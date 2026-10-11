import Whir.DuplexRefinement
import Whir.DuplexEncoding

/-! Structural DMV18 conditions for a public-compression *supermode* of #552.
Every node's whole 64-byte block is message data, including prescribed padding;
the tweak is template data. Restricting to canonical duplex blocks is permitted.
This avoids silently assuming a semantic frame encoder to be injective. Trees
are linear, root first, and all nonseed links occupy the complete CV field.
This module proves structural properties, not DMV's probabilistic theorem. -/
namespace Whir.DuplexFraming
open FiatShamirGame DuplexRefinement

/-- Actual public compression input, including adversarially chosen CVs. -/
structure Node where
  cv : Digest32
  block : Block64
  tweak : UInt64
  last : Bool

def tag (n : Node) : Nat := n.tweak.toNat / 2^56

def isSeed (n : Node) : Prop := tag n = 1 ∧ n.last = true

def isInternal (n : Node) : Prop :=
  (tag n = 2 ∨ tag n = 3 ∨ tag n = 4 ∨ tag n = 5 ∨ tag n = 9) ∧ n.last = true

def isTerminal (n : Node) : Prop :=
  (tag n = 6 ∨ tag n = 7 ∨ tag n = 8) ∧ n.last = true

instance (n : Node) : Decidable (isSeed n) := inferInstanceAs (Decidable (_ ∧ _))
instance (n : Node) : Decidable (isInternal n) := inferInstanceAs (Decidable (_ ∧ _))
instance (n : Node) : Decidable (isTerminal n) := inferInstanceAs (Decidable (_ ∧ _))

/-- Root-first body: internal nodes followed by exactly one seed. Chaining
positions are not inferred from message contents: they are always the CV field. -/
inductive Body : List Node → Prop where
  | seed {s} : isSeed s → Body [s]
  | step {n ns} : isInternal n → Body ns → Body (n :: ns)

def Complete (ns : List Node) : Prop :=
  ∃ t rest, ns = t :: rest ∧ isTerminal t ∧ Body rest

/-- An efficient deterministic parser for complete bodies. -/
def body? : List Node → Bool
  | [] => false
  | [s] => decide (isSeed s)
  | n :: m :: rest => decide (isInternal n) && body? (m :: rest)

 theorem body?_correct (ns : List Node) : body? ns = true ↔ Body ns := by
  induction ns with
  | nil => simp [body?]; intro h; cases h
  | cons n ns ih =>
    cases ns with
    | nil =>
      simp only [body?, decide_eq_true_eq]
      constructor
      · exact Body.seed
      · intro h; cases h with
        | seed h => exact h
        | step _ h => cases h
    | cons m ns =>
      simp only [body?, Bool.and_eq_true, decide_eq_true_eq]
      rw [ih]
      constructor
      · rintro ⟨hn, hr⟩; exact Body.step hn hr
      · intro h; cases h with | step hn hr => exact ⟨hn, hr⟩

 def complete? : List Node → Bool
  | [] => false
  | t :: rest => decide (isTerminal t) && body? rest

 theorem complete?_correct (ns : List Node) : complete? ns = true ↔ Complete ns := by
  cases ns with
  | nil => simp [complete?, Complete]
  | cons t rest => simp [complete?, Complete, body?_correct]

 theorem body_nonempty {ns : List Node} (h : Body ns) : ns ≠ [] := by cases h <;> simp

 theorem terminal_not_seed {n : Node} (ht : isTerminal n) : ¬isSeed n := by
  simp only [isTerminal, isSeed] at *; omega

 theorem terminal_not_internal {n : Node} (ht : isTerminal n) : ¬isInternal n := by
  simp only [isTerminal, isInternal] at *; omega

 theorem seed_not_internal {n : Node} (hs : isSeed n) : ¬isInternal n := by
  simp only [isSeed, isInternal] at *; omega

 theorem body_no_terminal {ns : List Node} (h : Body ns) :
    ∀ n ∈ ns, ¬isTerminal n := by
  induction h with
  | seed hs =>
    intro n hn ht
    simp only [List.mem_singleton] at hn
    subst n
    exact terminal_not_seed ht hs
  | step hi hb ih =>
    intro n hn ht
    rcases List.mem_cons.mp hn with rfl | hn
    · exact terminal_not_internal ht hi
    · exact ih n hn ht

theorem body_cons {n : Node} {ns : List Node} (h : Body (n :: ns)) :
    (ns = [] ∧ isSeed n) ∨ (isInternal n ∧ Body ns) := by
  cases h with
  | seed hs => exact Or.inl ⟨rfl, hs⟩
  | step hi hb => exact Or.inr ⟨hi, hb⟩

/-- A body's seed can never acquire descendants in another complete body. -/
theorem body_prefix_free {xs ys : List Node} (hx : Body xs) (hy : Body (xs ++ ys)) : ys = [] := by
  induction hx with
  | seed hs =>
    rcases body_cons hy with ⟨he, _⟩ | ⟨hi, _⟩
    · exact he
    · exact False.elim (seed_not_internal hs hi)
  | step hi hb ih =>
    rcases body_cons hy with ⟨he, hs⟩ | ⟨_, ht⟩
    · exact False.elim (seed_not_internal hs hi)
    · exact ih ht

/-- Every connected subtree of a linear compression tree is an interval.
No complete tree is a proper interval of any other complete tree. -/
 theorem subtree_free {pre tree suffix : List Node}
    (small : Complete tree) (large : Complete (pre ++ tree ++ suffix)) :
    pre = [] ∧ suffix = [] := by
  obtain ⟨t, rest, rfl, ht, hb⟩ := small
  cases pre with
  | nil =>
    simp only [List.nil_append, List.cons_append] at large
    obtain ⟨t', rest', he, _, hb'⟩ := large
    cases he
    exact ⟨rfl, body_prefix_free hb hb'⟩
  | cons p ps =>
    obtain ⟨t', rest', he, _, hb'⟩ := large
    simp only [List.cons_append, List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact False.elim (body_no_terminal hb' t (by simp) ht)

/-- Proper final subchains have a terminal followed only by internal nodes.
Their dangling radical is precisely the entire 256-bit CV of the last node. -/
def Radical (ns : List Node) : Prop :=
  ∃ t rest, ns = t :: rest ∧ isTerminal t ∧ ∀ n ∈ rest, isInternal n

 def radical? : List Node → Option Nat
  | [] => none
  | t :: rest =>
    if isTerminal t ∧ rest.all (fun n => decide (isInternal n)) then some rest.length else none

 theorem radical?_correct (ns : List Node) :
    (radical? ns).isSome = true ↔ Radical ns := by
  cases ns with
  | nil => simp [radical?, Radical]
  | cons t rest =>
    simp only [radical?, Radical, List.cons.injEq]
    split <;> simp_all

 theorem body_split {pre suffix : List Node} (h : Body (pre ++ suffix)) (hs : suffix ≠ []) :
    (∀ n ∈ pre, isInternal n) ∧ Body suffix := by
  induction pre with
  | nil => simpa using h
  | cons p ps ih =>
    rcases body_cons h with ⟨he, _⟩ | ⟨hn, hb⟩
    · have he' : ps ++ suffix = [] := he
      have hl := congrArg List.length he'
      simp only [List.length_append, List.length_nil] at hl
      exact False.elim (hs (List.length_eq_zero_iff.mp (by omega)))
    · obtain ⟨hp, ht⟩ := ih hb
      exact ⟨by intro n hm; rcases List.mem_cons.mp hm with rfl | hm; exact hn; exact hp n hm, ht⟩

 theorem final_subchain_radical {pre suffix : List Node}
    (h : Complete (pre ++ suffix)) (hp : pre ≠ []) (hs : suffix ≠ []) : Radical pre := by
  cases pre with
  | nil => exact False.elim (hp rfl)
  | cons t rest =>
    obtain ⟨t', rest', he, ht, hb⟩ := h
    simp only [List.cons_append, List.cons.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact ⟨t, rest, rfl, ht, (body_split hb hs).1⟩

/-- Every recognized radical is a proper final subchain of the supermode: a
single seed completes it, without changing the full-width dangling CV slot. -/
 theorem radical_extend {ns : List Node} (h : Radical ns) (s : Node) (hs : isSeed s) :
    Complete (ns ++ [s]) := by
  obtain ⟨t, rest, rfl, ht, hr⟩ := h
  refine ⟨t, rest ++ [s], rfl, ht, ?_⟩
  induction rest with
  | nil => exact Body.seed hs
  | cons n rest ih =>
    exact Body.step (hr n (by simp)) (ih (fun n hn => hr n (by simp [hn])))

/-- In the supermode the seed's CV input is extra message data, never a
chaining pointer. #552 restricts it to the fixed parameter IV. Other CV fields
are exclusively full-width chaining pointers, absent from message extraction. -/
def payload (n : Node) : Option Digest32 × Block64 :=
  (if isSeed n then some n.cv else none, n.block)

structure Extracted where
  message : List (Option Digest32 × Block64)
  template : List (UInt64 × Bool)

def extract (ns : List Node) : Option Extracted :=
  if complete? ns then some ⟨ns.map payload, ns.map (fun n => (n.tweak,n.last))⟩
  else none

/-- Chaining values are supplied by the generic tree interpreter, not returned
as part of the decoded message or used as template bits. -/
def rebuild : List (Option Digest32 × Block64) → List (UInt64 × Bool) → List Digest32 → List Node
  | (leaf,b) :: bs, (t,l) :: ts, cv :: cvs => ⟨leaf.getD cv,b,t,l⟩ :: rebuild bs ts cvs
  | _, _, _ => []

theorem rebuild_payload (ns : List Node) :
    rebuild (ns.map payload) (ns.map (fun n => (n.tweak,n.last))) (ns.map Node.cv) = ns := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
    simp only [List.map_cons, payload, rebuild]
    split <;> simp_all

/-- The complete raw message/template pair is efficiently decoded; malformed
trees are rejected. No injectivity or decoder-correctness premise is assumed. -/
theorem message_decodable (ns : List Node) (h : Complete ns) :
    ∃ e, extract ns = some e ∧ rebuild e.message e.template (ns.map Node.cv) = ns := by
  refine ⟨⟨ns.map payload, ns.map (fun n => (n.tweak,n.last))⟩, ?_, rebuild_payload ns⟩
  simp [extract, (complete?_correct ns).mpr h]

theorem extract_rejects (ns : List Node) (h : ¬Complete ns) : extract ns = none := by
  have hc : complete? ns = false := by
    cases he : complete? ns
    · rfl
    · exact False.elim (h ((complete?_correct ns).mp he))
  simp [extract, hc]

theorem packed_tag (cv : Digest32) (block : Block64) (r len previous : Nat)
    (hr : r < 256) (hl : len < 128) (hp : previous < 2^49) :
    tag ⟨cv,block,UInt64.ofNat (packTweak r len previous),true⟩ = r := by
  simp only [tag, UInt64.toNat_ofNat', packTweak]
  omega

theorem absorb_node_internal (cv : Digest32) (block : Block64) (first last : Bool)
    (len previous : Nat) (hl : len ≤ 64) (hp : previous ≤ maxCursor) :
    isInternal ⟨cv,block,absorbTweak first last len previous,true⟩ := by
  have hp' : previous < 2^49 := by unfold maxCursor at hp; omega
  have hl' : len < 128 := by omega
  have hr : role first last < 256 := by cases first <;> cases last <;> decide
  have ht := packed_tag cv block (role first last) len previous hr hl' hp'
  simp only [absorbTweak, isInternal]
  rw [ht]
  cases first <;> cases last <;> simp [role]

theorem seed_node (iv domain statement : Digest32) :
    isSeed ⟨iv,ByteCodec.pairBytes (domain,statement),UInt64.ofNat (2^56),true⟩ := by
  norm_num [isSeed, tag]

theorem nonce_node (cv : Digest32) (nonce : Scalar24) (previous bits : Nat) :
    isInternal ⟨cv,nonceBlock nonce previous bits,UInt64.ofNat (9*2^56),true⟩ := by
  norm_num [isInternal, tag]

def terminalNode (cv : Digest32) : Terminal → Node
  | .output block => ⟨cv,wordsBlock [block],UInt64.ofNat (6*2^56),true⟩
  | .commitment consumed => ⟨cv,wordsBlock [consumed],UInt64.ofNat (7*2^56),true⟩
  | .powBase consumed bits => ⟨cv,wordsBlock [consumed,bits],UInt64.ofNat (8*2^56),true⟩

theorem terminal_node (cv : Digest32) (t : Terminal) : isTerminal (terminalNode cv t) := by
  cases t <;> norm_num [terminalNode, isTerminal, tag]

theorem terminal_evaluation (c : Compression) (cv : Digest32) (t : Terminal) :
    c (terminalNode cv t).cv (terminalNode cv t).block
      (terminalNode cv t).tweak (terminalNode cv t).last = evalTerminal c cv t := by
  cases t <;> rfl

theorem body_has_seed {ns : List Node} (h : Body ns) : ∃ s ∈ ns, isSeed s := by
  induction h with
  | seed hs => exact ⟨_, by simp, hs⟩
  | step hi hb ih =>
    obtain ⟨s, hs, ht⟩ := ih
    exact ⟨s, by simp [hs], ht⟩

theorem radical_no_seed {ns : List Node} (h : Radical ns) : ∀ n ∈ ns, ¬isSeed n := by
  obtain ⟨t, rest, rfl, ht, hr⟩ := h
  intro n hn hs
  rcases List.mem_cons.mp hn with rfl | hn
  · exact terminal_not_seed ht hs
  · exact seed_not_internal hs (hr n hn)

theorem radical_not_complete {ns : List Node} (h : Radical ns) : ¬Complete ns := by
  rintro ⟨t,rest,rfl,ht,hb⟩
  obtain ⟨s,hs,hseed⟩ := body_has_seed hb
  exact radical_no_seed h s (by simp [hs]) hseed

/-- Universality of the radical, not merely a recognizer on valid examples:
in *every* complete tree containing a recognized interval, that interval
contains the root and omits the child of its last node. The missing link is
the last node's fixed full-width CV position, independent of its message. -/
theorem radical_universal {pre ns suffix : List Node} (h : Radical ns)
    (whole : Complete (pre ++ ns ++ suffix)) : pre = [] ∧ suffix ≠ [] := by
  have start : pre = [] := by
    obtain ⟨t,rest,rfl,ht,hr⟩ := h
    cases pre with
    | nil => rfl
    | cons p ps =>
      obtain ⟨t',rest',he,_,hb⟩ := whole
      simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl,rfl⟩ := he
      exact False.elim (body_no_terminal hb t (by simp) ht)
  refine ⟨start, ?_⟩
  intro he
  exact radical_not_complete h (by simpa [start, he] using whole)

/-- Seed-less recognized intervals cannot be leaf subtrees: every leaf subtree
of a linear complete tree contains that tree's seed. -/
theorem radical_not_leaf {ns : List Node} (h : Radical ns) :
    ¬ ∃ s ∈ ns, isSeed s := by
  rintro ⟨s,hs,hseed⟩
  exact radical_no_seed h s hs hseed

def nodeValue (c : Compression) (n : Node) : Digest32 := c n.cv n.block n.tweak n.last

/-- Compression-consistent tree instances: each internal node's entire CV
field is exactly its child's output. No hash/collision assumption is used. -/
inductive Tree (c : Compression) : Digest32 → List Node → Prop where
  | seed (n : Node) (h : isSeed n) : Tree c (nodeValue c n) [n]
  | step (n : Node) (ns : List Node) (h : isInternal n) (child : Tree c n.cv ns) :
      Tree c (nodeValue c n) (n :: ns)

theorem Tree.body {c : Compression} {cv : Digest32} {ns : List Node} (h : Tree c cv ns) :
    Body ns := by
  induction h with
  | seed n hn => exact Body.seed hn
  | step n ns hn ht ih => exact Body.step hn ih

def Bounds (s : State) : Prop :=
  s.pending.size ≤ 64 ∧ s.previous ≤ maxCursor ∧ s.consumed ≤ maxCursor

/-- Trace allocation is specification-only. Executable State has no nodes. -/
structure Traced where
  state : State
  nodes : List Node

def Traced.Valid (c : Compression) (t : Traced) : Prop :=
  Tree c t.state.cv t.nodes ∧ Bounds t.state

def shifted (s : State) : State :=
  if s.consumed = 0 then s else {s with previous := s.consumed, consumed := 0}

@[simp] theorem shifted_cv (s : State) : (shifted s).cv = s.cv := by
  unfold shifted; split <;> rfl

@[simp] theorem shifted_consumed (s : State) : (shifted s).consumed = 0 := by
  unfold shifted; split <;> simp_all

theorem shifted_bounds (s : State) (h : Bounds s) : Bounds (shifted s) := by
  unfold shifted; split
  · exact h
  · exact ⟨h.1,h.2.2,by simp [maxCursor]⟩

def absorbNode (s : State) (last : Bool) : Node :=
  ⟨s.cv,padded s.pending,absorbTweak s.first last s.pending.size s.previous,true⟩

def traceAbsorbByte (c : Compression) (t : Traced) (b : Byte) : Traced :=
  let s := shifted t.state
  {state := absorbByte c s b,
   nodes := if s.pending.size = 64 then absorbNode s false :: t.nodes else t.nodes}

theorem absorbByte_shifted (c : Compression) (s : State) (b : Byte) :
    absorbByte c (shifted s) b = absorbByte c s b := by
  unfold shifted
  split
  · rfl
  · rename_i hc; simp [absorbByte, hc]

@[simp] theorem traceAbsorbByte_state (c : Compression) (t : Traced) (b : Byte) :
    (traceAbsorbByte c t b).state = absorbByte c t.state b := absorbByte_shifted c t.state b

theorem absorbByte_bounds (c : Compression) (s : State) (b : Byte) (h : Bounds s) :
    Bounds (absorbByte c s b) := by
  rcases h with ⟨hb,hp,hc⟩
  by_cases hz : s.consumed = 0 <;> by_cases hf : s.pending.size = 64
  all_goals simp_all [absorbByte, Bounds, maxCursor] <;> omega

theorem traceAbsorbByte_valid (c : Compression) (t : Traced) (b : Byte) (h : t.Valid c) :
    (traceAbsorbByte c t b).Valid c := by
  have hb := shifted_bounds t.state h.2
  have ht : Tree c (shifted t.state).cv t.nodes := by simpa using h.1
  refine ⟨?_, absorbByte_bounds c _ b hb⟩
  have hc := shifted_consumed t.state
  by_cases hp : (shifted t.state).pending.size = 64
  · have hi := absorb_node_internal (shifted t.state).cv (padded (shifted t.state).pending)
      (shifted t.state).first false (shifted t.state).pending.size (shifted t.state).previous hb.1 hb.2.1
    have hn := Tree.step (c := c) (absorbNode (shifted t.state) false) t.nodes hi ht
    simpa only [traceAbsorbByte, hp, ↓reduceIte, absorbByte, hc, absorbNode, nodeValue] using hn
  · simpa only [traceAbsorbByte, hp, ↓reduceIte, absorbByte, hc] using ht

def traceAbsorb (c : Compression) (t : Traced) (bs : List Byte) : Traced :=
  bs.foldl (traceAbsorbByte c) t

@[simp] theorem traceAbsorb_state (c : Compression) (t : Traced) (bs : List Byte) :
    (traceAbsorb c t bs).state = absorb c t.state bs := by
  induction bs generalizing t with
  | nil => rfl
  | cons b bs ih =>
    simp only [traceAbsorb, absorb, List.foldl_cons] at *
    rw [ih, traceAbsorbByte_state]

theorem traceAbsorb_valid (c : Compression) (t : Traced) (bs : List Byte) (h : t.Valid c) :
    (traceAbsorb c t bs).Valid c := by
  induction bs generalizing t with
  | nil => exact h
  | cons b bs ih => exact ih _ (traceAbsorbByte_valid c t b h)

def traceFinish (c : Compression) (t : Traced) : Traced :=
  {state := finish c t.state,
   nodes := if t.state.pending.isEmpty then t.nodes else absorbNode t.state true :: t.nodes}

theorem traceFinish_valid (c : Compression) (t : Traced) (h : t.Valid c) :
    (traceFinish c t).Valid c := by
  by_cases hp : t.state.pending.isEmpty = true
  · simpa [traceFinish, finish, hp] using h
  · refine ⟨?_, ?_⟩
    · have hi := absorb_node_internal t.state.cv (padded t.state.pending)
        t.state.first true t.state.pending.size t.state.previous h.2.1 h.2.2.1
      have hn := Tree.step (c := c) (absorbNode t.state true) t.nodes hi h.1
      simpa [traceFinish, finish, hp, finalized, absorbNode, nodeValue] using hn
    · simpa [traceFinish, finish, hp, Bounds, maxCursor] using h.2.2.2

def traceSeed (c : Compression) (iv domain statement : Digest32) : Traced :=
  {state := seed c iv domain statement,
   nodes := [⟨iv,ByteCodec.pairBytes (domain,statement),UInt64.ofNat (2^56),true⟩]}

theorem traceSeed_valid (c : Compression) (iv domain statement : Digest32) :
    (traceSeed c iv domain statement).Valid c := by
  refine ⟨Tree.seed _ (seed_node iv domain statement), ?_⟩
  simp [traceSeed, seed, Bounds, maxCursor]


def traceFrame (c : Compression) (t : Traced) : Frame → Traced
  | .absorb previous bs =>
    traceFinish c (traceAbsorb c ⟨{cv := t.state.cv, previous := previous},t.nodes⟩ bs)
  | .nonce previous bits nonce =>
    let n : Node := ⟨t.state.cv,nonceBlock nonce previous bits,UInt64.ofNat (9*2^56),true⟩
    ⟨{cv := nodeValue c n},n :: t.nodes⟩

theorem traceFrame_cv (c : Compression) (t : Traced) (f : Frame) :
    (traceFrame c t f).state.cv = evalFrame c t.state.cv f := by
  cases f with
  | absorb previous bs =>
    simp only [traceFrame, traceFinish, finish_cv, traceAbsorb_state, evalFrame]
  | nonce previous bits nonce => rfl

theorem traceFrame_valid (c : Compression) (t : Traced) (f : Frame)
    (h : t.Valid c) (hf : DuplexEncoding.FrameValid f) : (traceFrame c t f).Valid c := by
  cases f with
  | absorb previous bs =>
    apply traceFinish_valid
    apply traceAbsorb_valid
    refine ⟨h.1, ?_⟩
    exact ⟨by simp, by change previous ≤ maxCursor; have := hf.1; unfold maxCursor; omega, by simp [maxCursor]⟩
  | nonce previous bits nonce =>
    refine ⟨Tree.step _ _ (nonce_node t.state.cv nonce previous bits) h.1, ?_⟩
    simp [traceFrame, Bounds, maxCursor]

def traceHistory (c : Compression) (iv : Digest32) (h : FramedHistory) : Traced :=
  h.frames.foldl (traceFrame c) (traceSeed c iv h.domain h.statement)

theorem traceFrame_fold_cv (c : Compression) (t : Traced) (fs : List Frame) :
    (fs.foldl (traceFrame c) t).state.cv = fs.foldl (evalFrame c) t.state.cv := by
  induction fs generalizing t with
  | nil => rfl
  | cons f fs ih => simp only [List.foldl_cons, ih, traceFrame_cv]

theorem traceHistory_cv (c : Compression) (iv : Digest32) (h : FramedHistory) :
    (traceHistory c iv h).state.cv = evalHistory c iv h := by
  exact traceFrame_fold_cv c _ _

theorem traceHistory_valid (c : Compression) (iv : Digest32) (h : FramedHistory)
    (admissible : ∀ f ∈ h.frames, DuplexEncoding.FrameValid f) : (traceHistory c iv h).Valid c := by
  have step : ∀ (fs : List Frame) (t : Traced), t.Valid c →
      (∀ f ∈ fs, DuplexEncoding.FrameValid f) → (fs.foldl (traceFrame c) t).Valid c := by
    intro fs
    induction fs with
    | nil => intro t ht _; exact ht
    | cons f fs ih =>
      intro t ht hf
      exact ih _ (traceFrame_valid c t f ht (hf f (by simp))) (fun g hg => hf g (by simp [hg]))
  exact step _ _ (traceSeed_valid c iv h.domain h.statement) admissible

def coordinateTree (c : Compression) (iv : Digest32) (q : Coordinate) : List Node :=
  let t := traceHistory c iv q.history
  terminalNode t.state.cv q.terminal :: t.nodes

theorem coordinateTree_complete (c : Compression) (iv : Digest32) (q : Coordinate)
    (admissible : ∀ f ∈ q.history.frames, DuplexEncoding.FrameValid f) :
    Complete (coordinateTree c iv q) := by
  exact ⟨_,_,rfl,terminal_node _ _,(traceHistory_valid c iv q.history admissible).1.body⟩

theorem coordinateTree_evaluates (c : Compression) (iv : Digest32) (q : Coordinate) :
    nodeValue c (terminalNode (traceHistory c iv q.history).state.cv q.terminal) =
      evalCoordinate c iv q := by
  have he := terminal_evaluation c (traceHistory c iv q.history).state.cv q.terminal
  change nodeValue c (terminalNode (traceHistory c iv q.history).state.cv q.terminal) = _ at he
  rw [he, traceHistory_cv]
  rfl

/-- Erase chaining fields to obtain the chronological primitive plan. -/
def rawPlan (ns : List Node) : List DuplexEncoding.Instruction :=
  ns.reverse.map (fun n => (n.block,n.tweak))

theorem trace_chunks (c : Compression) (t : Traced) (bs : List Byte)
    (cursor : t.state.consumed = 0) :
    rawPlan (traceFinish c (traceAbsorb c t bs)).nodes =
      rawPlan t.nodes ++ DuplexEncoding.chunks t.state.first t.state.previous t.state.pending.toList bs := by
  induction bs generalizing t with
  | nil =>
    by_cases hp : t.state.pending = #[]
    · simp [traceAbsorb, traceFinish, rawPlan, DuplexEncoding.chunks, hp]
    · simp [traceAbsorb, traceFinish, rawPlan, DuplexEncoding.chunks, DuplexEncoding.chunk,
        absorbNode, hp, Array.isEmpty_iff]
  | cons b bs ih =>
    change rawPlan (traceFinish c (traceAbsorb c (traceAbsorbByte c t b) bs)).nodes = _
    rw [ih _ (by rw [traceAbsorbByte_state]; exact absorbByte_cursor c t.state b)]
    by_cases hp : t.state.pending.size = 64
    · simp [traceAbsorbByte, shifted, cursor, hp, absorbByte, rawPlan, DuplexEncoding.chunks,
        DuplexEncoding.chunk, absorbNode, List.append_assoc]
    · simp [traceAbsorbByte, shifted, cursor, hp, absorbByte, rawPlan, DuplexEncoding.chunks]

theorem traceFrame_plan (c : Compression) (t : Traced) (f : Frame) :
    rawPlan (traceFrame c t f).nodes = rawPlan t.nodes ++ DuplexEncoding.framePlan f := by
  cases f with
  | absorb previous bs =>
    simpa only [traceFrame, DuplexEncoding.framePlan, Array.toList_empty] using
      trace_chunks c ⟨{cv := t.state.cv, previous := previous},t.nodes⟩ bs rfl
  | nonce previous bits nonce =>
    simp [traceFrame, rawPlan, DuplexEncoding.framePlan]

theorem traceFrames_plan (c : Compression) (t : Traced) (fs : List Frame) :
    rawPlan (fs.foldl (traceFrame c) t).nodes = rawPlan t.nodes ++ fs.flatMap DuplexEncoding.framePlan := by
  induction fs generalizing t with
  | nil => simp
  | cons f fs ih =>
    simp only [List.foldl_cons, ih, traceFrame_plan, List.flatMap_cons, List.append_assoc]

/-- The actual compression trace has exactly the independently encoded plan;
the template constructor does not query or depend on the compression oracle. -/
theorem coordinateTree_plan (c : Compression) (iv : Digest32) (q : Coordinate) :
    rawPlan (coordinateTree c iv q) = DuplexEncoding.plan q := by
  have h := traceFrames_plan c (traceSeed c iv q.history.domain q.history.statement) q.history.frames
  unfold coordinateTree rawPlan
  simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
  change rawPlan (traceHistory c iv q.history).nodes ++
    [((terminalNode (traceHistory c iv q.history).state.cv q.terminal).block,
      (terminalNode (traceHistory c iv q.history).state.cv q.terminal).tweak)] = _
  rw [show rawPlan (traceHistory c iv q.history).nodes =
    rawPlan (traceSeed c iv q.history.domain q.history.statement).nodes ++
      q.history.frames.flatMap DuplexEncoding.framePlan from h]
  unfold DuplexEncoding.plan
  cases q.terminal <;>
    simp [rawPlan, traceSeed, terminalNode, DuplexEncoding.terminalPlan]

def evalPlan (c : Compression) (cv : Digest32) (xs : List DuplexEncoding.Instruction) : Digest32 :=
  xs.foldl (fun cv i => c cv i.1 i.2 true) cv

theorem evalPlan_append (c : Compression) (cv : Digest32) (xs ys : List DuplexEncoding.Instruction) :
    evalPlan c cv (xs ++ ys) = evalPlan c (evalPlan c cv xs) ys := by
  simp [evalPlan, List.foldl_append]

theorem chunks_evaluate (c : Compression) (s : State) (bs : List Byte) (cursor : s.consumed = 0) :
    evalPlan c s.cv (DuplexEncoding.chunks s.first s.previous s.pending.toList bs) =
      finalized c (absorb c s bs) := by
  induction bs generalizing s with
  | nil =>
    by_cases hp : s.pending = #[]
    · simp [DuplexEncoding.chunks, hp, evalPlan, finalized]
    · simp [DuplexEncoding.chunks, DuplexEncoding.chunk, evalPlan, finalized, hp, Array.isEmpty_iff]
  | cons b bs ih =>
    change _ = finalized c (absorb c (absorbByte c s b) bs)
    rw [← ih _ (absorbByte_cursor c s b)]
    by_cases hp : s.pending.size = 64
    · simp [DuplexEncoding.chunks, DuplexEncoding.chunk, absorbByte, cursor, hp, evalPlan]
    · simp [DuplexEncoding.chunks, absorbByte, cursor, hp]

theorem framePlan_evaluate (c : Compression) (cv : Digest32) (f : Frame) :
    evalPlan c cv (DuplexEncoding.framePlan f) = evalFrame c cv f := by
  cases f with
  | absorb previous bs =>
    exact chunks_evaluate c {cv := cv, previous := previous} bs rfl
  | nonce previous bits nonce => rfl

theorem framesPlan_evaluate (c : Compression) (cv : Digest32) (fs : List Frame) :
    evalPlan c cv (fs.flatMap DuplexEncoding.framePlan) = fs.foldl (evalFrame c) cv := by
  induction fs generalizing cv with
  | nil => rfl
  | cons f fs ih =>
    simp only [List.flatMap_cons, evalPlan_append, framePlan_evaluate, List.foldl_cons, ih]

/-- Full executable-to-mode correspondence with no assumed framing bridge. -/
theorem plan_evaluate (c : Compression) (iv : Digest32) (q : Coordinate) :
    evalPlan c iv (DuplexEncoding.plan q) = evalCoordinate c iv q := by
  unfold DuplexEncoding.plan
  change evalPlan c (seed c iv q.history.domain q.history.statement).cv
    (q.history.frames.flatMap DuplexEncoding.framePlan ++ [DuplexEncoding.terminalPlan q.terminal]) = _
  rw [evalPlan_append, framesPlan_evaluate]
  unfold evalCoordinate evalHistory
  cases q.terminal <;> rfl

def extractedPlan (e : Extracted) : List DuplexEncoding.Instruction :=
  ((e.message.zip e.template).map (fun p => (p.1.2,p.2.1))).reverse

theorem extractedPlan_payload (ns : List Node) :
    extractedPlan ⟨ns.map payload, ns.map (fun n => (n.tweak,n.last))⟩ = rawPlan ns := by
  have he : ((ns.map payload).zip (ns.map (fun n => (n.tweak,n.last)))).map
      (fun p => (p.1.2,p.2.1)) = ns.map (fun n => (n.block,n.tweak)) := by
    induction ns with
    | nil => rfl
    | cons n ns ih => simp [payload, ih]
  simp only [extractedPlan, he, rawPlan, List.map_reverse]

theorem extract_plan (ns : List Node) (complete : Complete ns) :
    (extract ns).map extractedPlan = some (rawPlan ns) := by
  simp only [extract, (complete?_correct ns).mpr complete, ↓reduceIte, Option.map_some,
    extractedPlan_payload]

/-- Injectivity into the actual DMV message/template domain, not an assumed
abstract framing map. Holds even for trees evaluated using different public
compression functions; chaining fields never occur in the decoded message. -/
theorem canonical_mode_injective (c d : Compression) (iv : Digest32) {a b : Coordinate}
    (ha : DuplexEncoding.Admissible a) (hb : DuplexEncoding.Admissible b)
    (same : extract (coordinateTree c iv a) = extract (coordinateTree d iv b)) : a = b := by
  have h := congrArg (Option.map extractedPlan) same
  rw [extract_plan _ (coordinateTree_complete c iv a ha.1),
    extract_plan _ (coordinateTree_complete d iv b hb.1), coordinateTree_plan, coordinateTree_plan] at h
  exact DuplexEncoding.plan_injective ha hb (Option.some.inj h)

/-- These are concrete structural conditions of DMV18 Definitions 4--6.
The probabilistic public-random-compression theorem is a separate boundary. -/
theorem radical_subtree {ns : List Node} (h : Radical ns) :
    ∃ whole, Complete whole ∧ ∃ suffix, suffix ≠ [] ∧ whole = ns ++ suffix := by
  let s : Node := ⟨zeroDigest, ByteCodec.pairBytes (zeroDigest,zeroDigest), UInt64.ofNat (2^56), true⟩
  exact ⟨ns ++ [s], radical_extend h s (seed_node _ _ _), [s], by simp, rfl⟩

structure DMVConditions : Prop where
  subtreeFree : ∀ {pre tree suffix}, Complete tree → Complete (pre ++ tree ++ suffix) →
    pre = [] ∧ suffix = []
  radicalRecognizer : ∀ ns, (radical? ns).isSome = true ↔ Radical ns
  finalRadicals : ∀ {pre suffix}, Complete (pre ++ suffix) → pre ≠ [] → suffix ≠ [] → Radical pre
  radicalSubtree : ∀ {ns}, Radical ns →
    ∃ whole, Complete whole ∧ ∃ suffix, suffix ≠ [] ∧ whole = ns ++ suffix
  radicalUniversal : ∀ {pre ns suffix}, Radical ns → Complete (pre ++ ns ++ suffix) →
    pre = [] ∧ suffix ≠ []
  radicalNotLeaf : ∀ {ns}, Radical ns → ¬ ∃ s ∈ ns, isSeed s
  messageDecoder : ∀ ns, Complete ns →
    ∃ e, extract ns = some e ∧ rebuild e.message e.template (ns.map Node.cv) = ns
  decoderRejects : ∀ ns, ¬Complete ns → extract ns = none

theorem dmv_conditions : DMVConditions :=
  ⟨subtree_free, radical?_correct, final_subchain_radical, radical_subtree, radical_universal,
    radical_not_leaf, message_decodable, extract_rejects⟩

def HistoryValid (m : Model) : Prop := ∀ f ∈ m.history.frames, DuplexEncoding.FrameValid f

theorem closeRun_history_valid (m : Model) (hm : m.Valid) (h : HistoryValid m) :
    HistoryValid (closeRun m) := by
  by_cases hr : m.run = []
  · simpa [closeRun, hr] using h
  · intro f hf
    simp only [closeRun, hr, ↓reduceIte, List.mem_append, List.mem_singleton] at hf
    rcases hf with hf | rfl
    · exact h f hf
    · exact ⟨by have := hm.2.2.2; unfold maxCursor at this; omega, hr⟩

theorem reachable_history_valid (c : Compression) (iv domain statement : Digest32)
    {m : Model} {s : State} (h : Reachable c iv domain statement m s) : HistoryValid m := by
  induction h with
  | seed => simp [HistoryValid]
  | absorb h bs ih =>
    unfold modelAbsorb
    split <;> exact ih
  | squeeze h n ok ih =>
    have hm := (reachable_represents c iv domain statement h).1
    unfold modelSqueeze
    split
    · exact ih
    · exact closeRun_history_valid _ hm ih
  | nonce h nonce bits limit ih =>
    have hm := (reachable_represents c iv domain statement h).1
    have hc := closeRun_history_valid _ hm ih
    intro f hf
    simp only [modelNonce, List.mem_append, List.mem_singleton] at hf
    rcases hf with hf | rfl
    · exact hc f hf
    · refine ⟨?_, limit⟩
      rw [closeRun_consumed]
      have := hm.2.2.1
      unfold maxCursor at this
      omega

theorem reachable_closed_history_valid (c : Compression) (iv domain statement : Digest32)
    {m : Model} {s : State} (h : Reachable c iv domain statement m s) :
    HistoryValid (closeRun m) :=
  closeRun_history_valid m (reachable_represents c iv domain statement h).1
    (reachable_history_valid c iv domain statement h)

theorem reachable_commitment_admissible (c : Compression) (iv domain statement : Digest32)
    {m : Model} {s : State} (h : Reachable c iv domain statement m s) :
    DuplexEncoding.Admissible ⟨(closeRun m).history,.commitment m.consumed⟩ := by
  refine ⟨reachable_closed_history_valid c iv domain statement h, ?_⟩
  have := (reachable_represents c iv domain statement h).1.2.2.1
  change m.consumed < 2^49
  unfold maxCursor at this
  omega

theorem reachable_powBase_admissible (c : Compression) (iv domain statement : Digest32)
    {m : Model} {s : State} (h : Reachable c iv domain statement m s) (bits : Nat) (limit : bits ≤ 63) :
    DuplexEncoding.Admissible ⟨(closeRun m).history,.powBase m.consumed bits⟩ :=
  ⟨reachable_closed_history_valid c iv domain statement h,
    (reachable_commitment_admissible c iv domain statement h).2, limit⟩

/-- Charge the complete uncached seed-to-terminal path for each coordinate.
Direct public-primitive calls, other constructions, verification and PoW
trials remain additional global charges; this is not a cached-call bound. -/
def pathCost (q : Coordinate) : Nat := (DuplexEncoding.plan q).length

theorem coordinateTree_cost (c : Compression) (iv : Digest32) (q : Coordinate) :
    (coordinateTree c iv q).length = pathCost q := by
  have h := congrArg List.length (coordinateTree_plan c iv q)
  simpa [rawPlan, pathCost] using h

def Anchored (iv : Digest32) (ns : List Node) : Prop :=
  ∀ n ∈ ns, isSeed n → n.cv = iv

theorem anchored_internal (iv : Digest32) (n : Node) (ns : List Node)
    (hn : isInternal n) (h : Anchored iv ns) : Anchored iv (n :: ns) := by
  intro m hm hs
  rcases List.mem_cons.mp hm with rfl | hm
  · exact False.elim (seed_not_internal hs hn)
  · exact h m hm hs

theorem traceAbsorbByte_anchored (c : Compression) (iv : Digest32) (t : Traced) (b : Byte)
    (ht : t.Valid c) (h : Anchored iv t.nodes) : Anchored iv (traceAbsorbByte c t b).nodes := by
  have hb := shifted_bounds t.state ht.2
  by_cases hp : (shifted t.state).pending.size = 64
  · simp only [traceAbsorbByte, hp, ↓reduceIte]
    apply anchored_internal
    · exact absorb_node_internal _ _ _ _ _ _ hb.1 hb.2.1
    · exact h
  · simpa [traceAbsorbByte, hp] using h

theorem traceAbsorb_anchored (c : Compression) (iv : Digest32) (t : Traced) (bs : List Byte)
    (ht : t.Valid c) (h : Anchored iv t.nodes) : Anchored iv (traceAbsorb c t bs).nodes := by
  induction bs generalizing t with
  | nil => exact h
  | cons b bs ih =>
    exact ih _ (traceAbsorbByte_valid c t b ht) (traceAbsorbByte_anchored c iv t b ht h)

theorem traceFinish_anchored (c : Compression) (iv : Digest32) (t : Traced)
    (ht : t.Valid c) (h : Anchored iv t.nodes) : Anchored iv (traceFinish c t).nodes := by
  by_cases hp : t.state.pending.isEmpty = true
  · simpa [traceFinish, hp] using h
  · have hi := absorb_node_internal t.state.cv (padded t.state.pending) t.state.first true
      t.state.pending.size t.state.previous ht.2.1 ht.2.2.1
    simpa [traceFinish, hp] using anchored_internal iv (absorbNode t.state true) t.nodes hi h

theorem traceFrame_anchored (c : Compression) (iv : Digest32) (t : Traced) (f : Frame)
    (ht : t.Valid c) (h : Anchored iv t.nodes) (hf : DuplexEncoding.FrameValid f) :
    Anchored iv (traceFrame c t f).nodes := by
  cases f with
  | absorb previous bs =>
    have hstart : (Traced.mk {cv := t.state.cv, previous := previous} t.nodes).Valid c := by
      refine ⟨ht.1, by simp, ?_, by simp [maxCursor]⟩
      change previous ≤ maxCursor
      have := hf.1
      unfold maxCursor
      omega
    exact traceFinish_anchored c iv _ (traceAbsorb_valid c _ bs hstart)
      (traceAbsorb_anchored c iv _ bs hstart h)
  | nonce previous bits nonce =>
    exact anchored_internal iv _ _ (nonce_node t.state.cv nonce previous bits) h

theorem traceHistory_anchored (c : Compression) (iv : Digest32) (h : FramedHistory)
    (admissible : ∀ f ∈ h.frames, DuplexEncoding.FrameValid f) :
    Anchored iv (traceHistory c iv h).nodes := by
  have step : ∀ (fs : List Frame) (t : Traced), t.Valid c → Anchored iv t.nodes →
      (∀ f ∈ fs, DuplexEncoding.FrameValid f) → Anchored iv (fs.foldl (traceFrame c) t).nodes := by
    intro fs
    induction fs with
    | nil => intro _ _ ha _; exact ha
    | cons f fs ih =>
      intro t ht ha hf
      exact ih _ (traceFrame_valid c t f ht (hf f (by simp)))
        (traceFrame_anchored c iv t f ht ha (hf f (by simp))) (fun g hg => hf g (by simp [hg]))
  apply step _ _ (traceSeed_valid c iv h.domain h.statement) ?_ admissible
  intro n hn _
  simp only [traceSeed, List.mem_singleton] at hn
  subst n
  rfl

theorem coordinateTree_anchored (c : Compression) (iv : Digest32) (q : Coordinate)
    (h : DuplexEncoding.Admissible q) : Anchored iv (coordinateTree c iv q) := by
  intro n hn hs
  rcases List.mem_cons.mp hn with rfl | hn
  · exact False.elim (terminal_not_seed (terminal_node _ _) hs)
  · exact traceHistory_anchored c iv q.history h.1 n hn hs

theorem body_flags {ns : List Node} (h : Body ns) : ∀ n ∈ ns, n.last = true := by
  induction h with
  | seed hs => simpa using hs.2
  | step hi hb ih =>
    intro n hn
    rcases List.mem_cons.mp hn with rfl | hn
    · exact hi.2
    · exact ih n hn

theorem complete_flags {ns : List Node} (h : Complete ns) : ∀ n ∈ ns, n.last = true := by
  obtain ⟨t,rest,rfl,ht,hb⟩ := h
  intro n hn
  rcases List.mem_cons.mp hn with rfl | hn
  · exact ht.2
  · exact body_flags hb n hn

/-- Concrete DMV (message,template) coordinate, computable without compression.
All seed CV bits are fixed to the primitive parameter IV in this submode. -/
def keyFromPlan (iv : Digest32) (p : List DuplexEncoding.Instruction) : Extracted :=
  {message := p.reverse.map (fun i => (if DuplexEncoding.readRole i.2 = 1 then some iv else none, i.1)),
   template := p.reverse.map (fun i => (i.2,true))}

def modeKey (iv : Digest32) (q : Coordinate) : Extracted := keyFromPlan iv (DuplexEncoding.plan q)

theorem extract_anchored (iv : Digest32) (ns : List Node)
    (hc : Complete ns) (ha : Anchored iv ns) :
    extract ns = some (keyFromPlan iv (rawPlan ns)) := by
  have hf := complete_flags hc
  simp only [extract, (complete?_correct ns).mpr hc, ↓reduceIte, keyFromPlan, rawPlan,
    ← List.map_reverse, List.reverse_reverse, List.map_map]
  congr 2
  · apply List.map_congr_left
    intro n hn
    have hnflag := hf n hn
    by_cases hs : isSeed n
    · have ht := hs.1
      unfold tag at ht
      simp only [payload, hs, ↓reduceIte, Function.comp_apply, DuplexEncoding.readRole, ht, ha n hn hs]
    · have htag : tag n ≠ 1 := by intro he; exact hs ⟨he,hnflag⟩
      unfold tag at htag
      simp only [payload, hs, ↓reduceIte, Function.comp_apply, DuplexEncoding.readRole, htag]
  · apply List.map_congr_left
    intro n hn
    simp only [Function.comp_apply, hf n hn]

/-- The actual raw-mode key is independent of all compression outputs, not an
assumed parsing or state-correctness bridge. -/
theorem coordinateTree_key (c : Compression) (iv : Digest32) (q : Coordinate)
    (h : DuplexEncoding.Admissible q) :
    extract (coordinateTree c iv q) = some (modeKey iv q) := by
  rw [extract_anchored iv _ (coordinateTree_complete c iv q h.1) (coordinateTree_anchored c iv q h),
    coordinateTree_plan]
  rfl

theorem modeKey_injective (iv : Digest32) {a b : Coordinate}
    (ha : DuplexEncoding.Admissible a) (hb : DuplexEncoding.Admissible b)
    (same : modeKey iv a = modeKey iv b) : a = b := by
  have he : extractedPlan (modeKey iv a) = extractedPlan (modeKey iv b) := congrArg extractedPlan same
  have recover : ∀ q, extractedPlan (modeKey iv q) = DuplexEncoding.plan q := by
    intro q
    unfold modeKey keyFromPlan extractedPlan
    have step : ∀ p : List DuplexEncoding.Instruction,
      ((p.map (fun i => (if DuplexEncoding.readRole i.2 = 1 then some iv else none,i.1))).zip
        (p.map (fun i => (i.2,true)))).map (fun p => (p.1.2,p.2.1)) = p := by
      intro p; induction p with
      | nil => rfl
      | cons i p ih => simp [ih]
    rw [step, List.reverse_reverse]
  rw [recover a, recover b] at he
  exact DuplexEncoding.plan_injective ha hb he

/-- Box each intermediate reply over stored bytes before it becomes another
CV. The data-valued fold is essential: a Digest32-valued helper can be eta
expanded into a byte function that recomputes the whole predecessor chain.
This evaluator allocates neither mode Programs nor public execution traces. -/
private def evalPlanStoredResult (c : Compression) (cv : Digest32) :
    List DuplexEncoding.Instruction → Option Digest32
  | [] => some cv
  | i :: rest =>
    let bytes := Array.ofFn (c cv i.1 i.2 true)
    evalPlanStoredResult c (fun j => bytes[j.val]'(by
      simp only [bytes,Array.size_ofFn]
      exact j.isLt)) rest

private theorem evalPlanStoredResult_eq (c : Compression) (cv : Digest32)
    (xs : List DuplexEncoding.Instruction) :
    evalPlanStoredResult c cv xs = some (evalPlan c cv xs) := by
  induction xs generalizing cv with
  | nil => rfl
  | cons i rest ih => simp [evalPlanStoredResult,ih,evalPlan]

def evalCoordinateStored (c : Compression) (iv : Digest32) (q : Coordinate) : Digest32 :=
  let result := evalPlanStoredResult c iv (DuplexEncoding.plan q)
  result.get (by simp only [result,evalPlanStoredResult_eq,Option.isSome_some])

/-- Checked runtime refinement for the actual construction evaluator; the
logical semantics, all compression inputs, and all resource bounds are unchanged. -/
@[csimp] theorem evalCoordinate_stored : evalCoordinate = evalCoordinateStored := by
  funext c iv q
  simp only [evalCoordinateStored,evalPlanStoredResult_eq,Option.get_some,plan_evaluate]

/-- A data-valued consumer can force the complete construction once, rather
than invoking the Digest32-valued wrapper separately for each requested byte. -/
def withCoordinate {Result : Type} (c : Compression) (iv : Digest32) (q : Coordinate)
    (next : Digest32 → Result) : Result :=
  let result := evalPlanStoredResult c iv (DuplexEncoding.plan q)
  next (result.get (by simp only [result,evalPlanStoredResult_eq,Option.isSome_some]))

theorem withCoordinate_eq {Result : Type} (c : Compression) (iv : Digest32) (q : Coordinate)
    (next : Digest32 → Result) :
    withCoordinate c iv q next = next (evalCoordinate c iv q) := by
  simp only [withCoordinate,evalPlanStoredResult_eq,Option.get_some,plan_evaluate]

end Whir.DuplexFraming
