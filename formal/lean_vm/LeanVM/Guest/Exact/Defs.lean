/-
  LeanVM.Guest.Exact.Defs

  A computed hint is exact when what it writes is what the executor computes from what it reads
  (`Exec.runHint`); a call tree is exact when every hint on every path is. A hint pinned by the
  atom after it is exact on every valuation holding that atom (`inverse_exact`).
-/

module

public import LeanVM.Guest.Pops
public import Statement.Prover.Execute

/-!
# Exact hints

`Atom.Holds (.hint _)` is `True`: a valid tree may hold any words at a hint's outputs. The
executor computes them (`Exec.runHint`), so its completeness needs a reference whose words there are
the computed ones (`HintOk`). `Hint.Exact rd σ h`: the words `h` writes (`Dest.words`, a heap
destination's through `rd`) are the executor's formula applied to the words it reads, word for
word as `runHint` writes them (`bitWord`, `wordNat`, `g^n`); witness hints and allocations are
exact (`pops` and the allocator speak for them). `Tree.Exact P rd t`: every hint event on every
path of every instance of `t` is exact.

`inverse_exact`: the guest follows each `inverse` hint with `assertNe` on the same two values,
which pins it. `Stmt.blockNextOk p q` is the syntactic form, decided per function by the kernel
(`Exact/InverseCheck.lean`): every atom satisfying `p` is followed, in its block, by an atom `b`
with `q a b`. `walk_partnered`: then every such atom on a path has its partner on the path;
`inverse_exact_of_walk`: so every `inverse` hint of a valid instance of such a function is exact,
on every reader, with no hypothesis on the instance.
-/

namespace LeanVM.Guest.Core

open LeanVM.Parameters LeanVM.Semantics
open LeanVM.Prover.Exec (wordNat bitWord)

@[expose] public section

/-- The integer of a run of bit words, a nonzero word a set bit (`log2Ceil`'s read). -/
def bitsNat (ws : List E) (nbits : ℕ) : ℕ :=
  (List.range nbits).foldl (fun w j ↦ if ws.getD j 0 = 0 then w else w + 2 ^ j) 0

/-- `⌈log₂⌉` of an integer, `0` below `2` (`log2Ceil`). -/
def clog2 (word : ℕ) : ℕ := if word ≤ 1 then 0 else Nat.log2 (word - 1) + 1

/-- **What a computed hint writes is the executor's formula** of what it reads, on `σ` and `rd`. -/
def Hint.Exact (rd : Reader) (σ : Val) : Hint → Prop
  | .bits v start nbits d =>
    d.words rd σ = (List.range nbits).map fun j ↦ bitWord ((wordNat (σ v)).testBit (start + j))
  | .bitsExp v nbits d => ∃ n, n < 2 ^ nbits ∧ σ v = ofK (g ^ n) ∧
    d.words rd σ = (List.range nbits).map fun j ↦ bitWord (n.testBit j)
  | .digitsExp v nbits ndigits digitBits start startCell d => ∃ n st, n < 2 ^ nbits ∧
    σ v = ofK (g ^ n) ∧
    (match startCell with
      | none => st = start
      | some c => st < 2 ^ 7 ∧ σ c = ofK (g ^ st)) ∧
    d.words rd σ = (List.range ndigits).map fun j ↦ ofK (g ^
      (if 128 ≤ st + digitBits * j then 0 else (n >>> (st + digitBits * j)) % 2 ^ digitBits))
  | .windowsExp v start width count d =>
    d.words rd σ = (List.range count).map fun i ↦
      ofK (g ^ ((wordNat (σ v) >>> (start + i * width)) % 2 ^ width))
  | .limbs v ds =>
    ds.map σ = (List.range ds.length).map fun j ↦ ofK (if j = 0 then (σ v).limb 0 else (σ v).limb 1)
  | .log2Ceil b nbits floor dst => σ dst = ofK (g ^ max (clog2 (bitsNat (b.words rd σ) nbits)) floor)
  | .inverse x dst => σ dst = if σ x = 0 then 0 else (σ x)⁻¹
  | .witness .. => True
  | .alloc .. => True
  | .allocDyn .. => True

/-- An atom is exact: a hint's words, nothing for the others. -/
def Atom.Exact (rd : Reader) (σ : Val) : Atom → Prop
  | .hint h => h.Exact rd σ
  | _ => True

/-- **`inverse` then `assertNe` on the same values**: the hint's word is the inverse. -/
theorem inverse_exact {rd : Reader} {σ : Val} {x i p : V} (h : (Atom.assertNe x i p).Holds rd σ) :
    (Hint.inverse x i).Exact rd σ := by
  obtain ⟨h1, h2⟩ := h
  have hm : σ x * σ i = 1 := h1.symm.trans h2
  have hx : σ x ≠ 0 := left_ne_zero_of_mul_eq_one hm
  show σ i = if σ x = 0 then 0 else (σ x)⁻¹
  rw [ite_eq_right hx, inv_eq_of_mul_eq_one_right hm]

/-! ## Pinned by the next atom -/

/-- An atom heading `rest` passes: unless it satisfies `p`, the next statement is an atom `b`
with `q a b`. -/
def Stmt.headOk (p : Atom → Bool) (q : Atom → Atom → Bool) : Atom → List Stmt → Bool
  | a, .atom b :: _ => !p a || q a b
  | a, _ => !p a

mutual
/-- **Every atom satisfying `p` is followed, in its block, by an atom `b` with `q a b`**, in the
block and in the blocks nested in it. -/
def Stmt.blockNextOk (p : Atom → Bool) (q : Atom → Atom → Bool) : List Stmt → Bool
  | [] => true
  | .atom a :: rest => Stmt.headOk p q a rest && Stmt.blockNextOk p q rest
  | .ite _ z n :: rest =>
    (Stmt.blockNextOk p q z && Stmt.blockNextOk p q n) && Stmt.blockNextOk p q rest
  | .match_ _ arms :: rest => Stmt.armsNextOk p q arms && Stmt.blockNextOk p q rest
  | .call .. :: rest => Stmt.blockNextOk p q rest
  | .callIf .. :: rest => Stmt.blockNextOk p q rest
  | .dispatch .. :: rest => Stmt.blockNextOk p q rest
  | .ret _ :: rest => Stmt.blockNextOk p q rest

/-- `Stmt.blockNextOk` of every arm. -/
def Stmt.armsNextOk (p : Atom → Bool) (q : Atom → Atom → Bool) : List (List Stmt) → Bool
  | [] => true
  | a :: as => Stmt.blockNextOk p q a && Stmt.armsNextOk p q as
end

/-- An `inverse` hint. -/
def isInverse : Atom → Bool
  | .hint (.inverse ..) => true
  | _ => false

/-- `assertNe` on the hint's two values. -/
def pinsInverse : Atom → Atom → Bool
  | .hint (.inverse x i), .assertNe x' i' _ => x == x' && i == i'
  | _, _ => false

end
end LeanVM.Guest.Core

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-- An event is exact: an atom's. -/
def Ev.Exact (rd : Reader) (σ : Val) : Ev → Prop
  | .atom a => a.Exact rd σ
  | _ => True

mutual
/-- **An exact call tree**: every hint on every instance's path is exact. -/
def Tree.Exact (P : Core.Program) (rd : Reader) : Tree → Prop
  | t@(.node _ σ _ kids) => (∀ e ∈ t.events P, e.Exact rd σ) ∧ Tree.ExactKids P rd kids
  | .phantom .. => True

/-- `Tree.Exact` of each callee. -/
def Tree.ExactKids (P : Core.Program) (rd : Reader) : List Tree → Prop
  | [] => True
  | k :: ks => k.Exact P rd ∧ Tree.ExactKids P rd ks
end

end
end LeanVM.Guest.Memory

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-! ## Pinned along a path -/

/-- An outcome's events, none when stuck. -/
def Out.evs : Out → List Ev
  | .fall es => es
  | .ret es _ => es
  | .stuck => []

variable {p : Atom → Bool} {q : Atom → Atom → Bool} {σ : Val}

/-- Events in which each atom satisfying `p` has a partner `b`, `q a b`. -/
def Partnered (p : Atom → Bool) (q : Atom → Atom → Bool) (es : List Ev) : Prop :=
  ∀ a, Ev.atom a ∈ es → p a = true → ∃ b, Ev.atom b ∈ es ∧ q a b = true

theorem Partnered.append {l l' : List Ev} (h : Partnered p q l) (h' : Partnered p q l') :
    Partnered p q (l ++ l') := by
  intro a ha hp
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨b, hb, hq⟩ := h a ha hp; exact ⟨b, List.mem_append_left _ hb, hq⟩
  · obtain ⟨b, hb, hq⟩ := h' a ha hp; exact ⟨b, List.mem_append_right _ hb, hq⟩

theorem partnered_noAtom {l : List Ev} (h : ∀ a, Ev.atom a ∉ l) : Partnered p q l :=
  fun a ha _ => absurd ha (h a)

theorem partnered_pre {es : List Ev} (h : Partnered p q es) :
    ∀ {o : Out}, Partnered p q o.evs → Partnered p q (o.pre es).evs
  | .fall _, h' | .ret _ _, h' => h.append h'
  | .stuck, _ => partnered_noAtom (by simp [Out.pre, Out.evs])

theorem partnered_seq {k : Out} (hk : Partnered p q k.evs) :
    ∀ {o : Out}, Partnered p q o.evs → Partnered p q (o.seq k).evs
  | .fall _, h => partnered_pre h hk
  | .ret _ _, h => h
  | .stuck, _ => partnered_noAtom (by simp [Out.seq, Out.evs])

theorem partnered_pick {x : V} {args rets : List V} :
    ∀ (j : ℕ) (fs : List String), Partnered p q (pick σ x args rets j fs).evs
  | _, [] => partnered_noAtom (by simp [pick, Out.evs])
  | j, f :: fs => by
    unfold pick
    split
    · exact partnered_noAtom (by simp [Out.evs])
    · exact partnered_pick (j + 1) fs

/-- An atom heading a block is among its events, if it does not get stuck. -/
theorem head_mem_walk (b : Atom) (r : List Stmt) :
    (walk σ (.atom b :: r)).evs = [] ∨ Ev.atom b ∈ (walk σ (.atom b :: r)).evs := by
  rw [walk, walk1]
  cases walk σ r <;> simp [Out.seq, Out.pre, Out.evs]

mutual
/-- **A block whose atoms satisfying `p` are each followed by a partner** has its partners on its
path. -/
theorem walk_partnered : ∀ (ss : List Stmt), Stmt.blockNextOk p q ss = true →
    Partnered p q (walk σ ss).evs
  | [], _ => partnered_noAtom (by simp [walk, Out.evs])
  | .atom a :: rest, h => by
    rw [Stmt.blockNextOk, Bool.and_eq_true] at h
    have hr := h.2
    have ih := walk_partnered rest hr
    have e : walk σ (.atom a :: rest) = (walk σ rest).pre [.atom a] := by rw [walk, walk1]; rfl
    rw [e]
    cases hw : walk σ rest with
    | stuck => exact partnered_noAtom (by simp [Out.pre, Out.evs])
    | fall es | ret es _ =>
      rw [hw] at ih
      intro a' ha' hp
      simp only [Out.pre, Out.evs, List.singleton_append, List.mem_cons, Ev.atom.injEq] at ha'
      rcases ha' with rfl | ha'
      · cases rest with
        | nil => simp [Stmt.headOk, hp] at h
        | cons s r =>
          cases s with
          | atom b =>
            have hq : q a' b = true := by
              have h1 := h.1
              simp only [Stmt.headOk, hp, Bool.not_true, Bool.false_or] at h1
              exact h1
            rcases head_mem_walk (σ := σ) b r with h0 | hb
            · rw [hw] at h0; simp only [Out.evs] at h0; subst h0
              simp [walk, walk1, Out.seq, Out.pre] at hw
              cases hr' : walk σ r <;> rw [hr'] at hw <;> simp at hw
            · rw [hw] at hb
              exact ⟨b, by simp only [Out.pre, Out.evs]; exact List.mem_cons_of_mem _ hb, hq⟩
          | _ => simp [Stmt.headOk, hp] at h
      · obtain ⟨b, hb, hq⟩ := ih a' ha' hp
        exact ⟨b, by simp only [Out.pre, Out.evs]; exact List.mem_cons_of_mem _ hb, hq⟩
  | .ite c z n :: rest, h => by
    simp only [Stmt.blockNextOk, Bool.and_eq_true] at h
    rw [walk, walk1]
    refine partnered_seq (walk_partnered rest h.2) (partnered_pre (partnered_noAtom (by simp)) ?_)
    split
    · exact walk_partnered z h.1.1
    · exact walk_partnered n h.1.2
  | .match_ x arms :: rest, h => by
    simp only [Stmt.blockNextOk, Bool.and_eq_true] at h
    rw [walk, walk1]
    exact partnered_seq (walk_partnered rest h.2) (walkArms_partnered x 0 arms h.1)
  | .call _ _ _ :: rest, h => by
    rw [Stmt.blockNextOk] at h
    rw [walk, walk1]
    exact partnered_seq (walk_partnered rest h) (partnered_noAtom (by simp [Out.evs]))
  | .callIf c _ _ :: rest, h => by
    rw [Stmt.blockNextOk] at h
    rw [walk, walk1]
    refine partnered_seq (walk_partnered rest h) (partnered_noAtom ?_)
    intro a ha
    simp only [Out.evs, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with ha | ha
    · cases ha
    · split at ha <;> cases ha
  | .dispatch _ _ _ _ :: rest, h => by
    rw [Stmt.blockNextOk] at h
    rw [walk, walk1]
    exact partnered_seq (walk_partnered rest h) (partnered_pick 0 _)
  | .ret _ :: rest, h => by
    rw [walk, walk1]
    exact partnered_noAtom (by simp [Out.seq, Out.evs])

/-- `walk_partnered` for the arms of a `match`. -/
theorem walkArms_partnered (x : V) : ∀ (j : ℕ) (as : List (List Stmt)), Stmt.armsNextOk p q as = true →
    Partnered p q (walkArms σ x j as).evs
  | _, [], _ => partnered_noAtom (by simp [walkArms, Out.evs])
  | j, a :: as, h => by
    simp only [Stmt.armsNextOk, Bool.and_eq_true] at h
    rw [walkArms]
    split
    · exact walk_partnered a h.1
    · exact walkArms_partnered x (j + 1) as h.2
end

/-- **On every valid instance of a function whose `inverse` hints are pinned, they are exact.** -/
theorem inverse_exact_of_walk {P : Core.Program} {rd : Reader} {f : String} {fn : Fn} {bufs : List ℕ}
    {kids : List Tree} {args rets : List E} (hv : (Tree.node f σ bufs kids).Valid P rd args rets)
    (hf : P.find? f = some fn) (hpin : Stmt.blockNextOk isInverse pinsInverse fn.body = true)
    {x i : V} (he : Ev.atom (.hint (.inverse x i)) ∈ (Tree.node f σ bufs kids).events P) :
    (Hint.inverse x i).Exact rd σ := by
  obtain ⟨fn', hf', -, es, vs, hw, -, hes, -⟩ := hv
  rw [hf] at hf'; cases hf'
  have hev : (Tree.node f σ bufs kids).events P = es := by
    simp only [Tree.events, Tree.name, Tree.val, hf, hw]
  rw [hev] at he
  have hp := walk_partnered (σ := σ) fn.body hpin
  rw [hw] at hp
  obtain ⟨b, hb, hq⟩ := hp _ he rfl
  cases b with
  | assertNe x' i' p' =>
    simp only [pinsInverse, Bool.and_eq_true, beq_iff_eq] at hq
    obtain ⟨rfl, rfl⟩ := hq
    exact inverse_exact (hes _ hb)
  | _ => simp [pinsInverse] at hq

end
end LeanVM.Guest.Memory
