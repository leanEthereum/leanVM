/-
  LeanVM.Guest.B1.Sig.BlockPops

  The witness-stream entries the signature templates' blocks pop: a block of atoms its hints', a block without witness hints none (the Keccak message among them), a WOTS chain walk and a codeword arm their chains' starts.
-/

module

public import LeanVM.Guest.B1.Sig.WotsSound
public import LeanVM.Guest.Pops

/-!
# The templates' pops

* `atomsPops`, `fallPops_atoms`: a block of atoms pops its hints' entries;
* `quiet`, `fallPops_quiet`, `kMsg_quiet`: a block of atoms without witness hints pops nothing;
* `fallPops_map`: statements in turn pop their entries in turn;
* `walkT_pops`, `walksT_pops`, `armT_pops`: a codeword arm pops its chains' starts, in chain order.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Memory

@[expose] public section

variable {rd : Reader}

/-! ## Blocks of atoms -/

/-- The entries a block's atoms pop. -/
def atomsPops (rd : Reader) (σ : Val) (ss : List Stmt) : List Pop :=
  ss.flatMap fun | .atom a => a.pops rd σ | _ => []

theorem fallPops_atoms (σ : Val) : ∀ {ss : List Stmt}, atomsOnly ss = true → FallPops rd σ ss (atomsPops rd σ ss)
  | [], _ => FallPops.nil
  | .atom a :: ss, h => by
      simp only [atomsOnly] at h
      have := (fallPops_atoms σ h).cons_atom (a := a)
      simpa [atomsPops] using this
  | .ite .. :: _, h | .match_ .. :: _, h | .call .. :: _, h | .callIf .. :: _, h
  | .dispatch .. :: _, h | .ret _ :: _, h => by simp [atomsOnly] at h

/-- Statements in turn pop their entries in turn. -/
theorem fallPops_map {α : Type} {σ : Val} (f : α → Stmt) (g : α → List Pop) :
    ∀ l : List α, (∀ a ∈ l, FallPops rd σ [f a] (g a)) → FallPops rd σ (l.map f) (l.flatMap g)
  | [], _ => FallPops.nil
  | a :: l, h => by
      rw [List.map_cons, List.flatMap_cons, ← List.singleton_append]
      exact (h a (by simp)).append (fallPops_map f g l fun b hb => h b (by simp [hb]))

theorem FallPops.congr_pops {σ : Val} {ss : List Stmt} {p q : List Pop} (h : FallPops rd σ ss p) (e : p = q) :
    FallPops rd σ ss q := e ▸ h

/-! ## Blocks without witness hints -/

/-- An atom that is no witness hint. -/
def atomQuiet : Atom → Bool
  | .hint (.witness ..) => false
  | _ => true

/-- All statements are atoms, none a witness hint. -/
def quiet : List Stmt → Bool
  | [] => true
  | .atom a :: ss => atomQuiet a && quiet ss
  | _ :: _ => false

theorem quiet_append : ∀ (xs ys : List Stmt), quiet (xs ++ ys) = (quiet xs && quiet ys)
  | [], _ => by simp [quiet]
  | .atom _ :: xs, ys => by simp only [List.cons_append, quiet, quiet_append xs ys, Bool.and_assoc]
  | .ite .. :: _, _ | .match_ .. :: _, _ | .call .. :: _, _ | .callIf .. :: _, _
  | .dispatch .. :: _, _ | .ret _ :: _, _ => by simp [quiet]

theorem quiet_flatMap {α : Type} (f : α → List Stmt) (hf : ∀ a, quiet (f a) = true) :
    ∀ l : List α, quiet (l.flatMap f) = true
  | [] => rfl
  | a :: l => by rw [List.flatMap_cons, quiet_append, hf a, quiet_flatMap f hf l]; rfl

/-- **A block without witness hints pops nothing.** -/
theorem fallPops_quiet (σ : Val) : ∀ {ss : List Stmt}, quiet ss = true → FallPops rd σ ss []
  | [], _ => FallPops.nil
  | .atom a :: ss, h => by
      simp only [quiet, Bool.and_eq_true] at h
      have hp : a.pops rd σ = [] := by
        cases a with
        | hint x => cases x <;> simp_all [atomQuiet, Atom.pops, Hint.pops]
        | _ => rfl
      simpa [hp] using (fallPops_quiet σ h.2).cons_atom (a := a)
  | .ite .. :: _, h | .match_ .. :: _, h | .call .. :: _, h | .callIf .. :: _, h
  | .dispatch .. :: _, h | .ret _ :: _, h => by simp [quiet] at h

/-! ## The Keccak message -/

theorem kCell_quiet (pad : Nat) (k : KC) (b : Nat) : quiet (kCell pad k b).1 = true := by
  cases k with
  | zero => rfl
  | const c => rw [kCell_const]; split <;> rfl
  | cell v => rfl

theorem kRunFresh_quiet : ∀ (ks : List KC) (b : Nat), quiet (kRunFresh ks b) = true
  | [], _ => rfl
  | .zero :: ks, b => kRunFresh_quiet ks (b + 1)
  | .const _ :: ks, b => kRunFresh_quiet ks (b + 1)
  | .cell _ :: ks, b => kRunFresh_quiet ks (b + 1)

theorem kRun_quiet (pad : Nat) (ks : List KC) (tailRun : Bool) (b : Nat) :
    quiet (kRun pad ks tailRun b).1 = true := by
  unfold kRun
  split_ifs
  · rfl
  · rfl
  · split
    · split_ifs
      · rfl
      · exact kRunFresh_quiet _ _
    · exact kRunFresh_quiet _ _

theorem kXor_quiet (pad : Nat) (st : V) (k : KC) (b : Nat) : quiet (kXor pad st k b).1 = true := by
  cases k with
  | zero => rfl
  | const c =>
      show quiet ((kCell pad _ b).1 ++ _) = true
      rw [quiet_append, kCell_quiet]; rfl
  | cell v => rfl

theorem kTailXor_quiet (pad : Nat) : ∀ (sts : List V) (ks : List KC) (b : Nat),
    quiet (kTailXor pad sts ks b).1 = true
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | st :: sts, k :: ks, b => by
      cases k with
      | zero =>
          show quiet ([copyS (.n b) st] ++ _) = true
          rw [quiet_append, kTailXor_quiet pad sts ks]; rfl
      | const c =>
          show quiet ((kXor pad st (.const c) b).1 ++ _) = true
          rw [quiet_append, kXor_quiet, kTailXor_quiet pad sts ks]; rfl
      | cell v =>
          show quiet ((kXor pad st (.cell v) b).1 ++ _) = true
          rw [quiet_append, kXor_quiet, kTailXor_quiet pad sts ks]; rfl

theorem kIns_quiet (pad : Nat) (blk : List KC) (tailRun : Bool) (st : Option (List V)) (b : Nat) :
    quiet (kIns pad blk tailRun st b).1 = true := by
  cases st with
  | none => simp [kIns, quiet_append, kCell_quiet, kRun_quiet]
  | some st =>
      simp only [kIns]
      split <;> simp [quiet_append, kXor_quiet, kTailXor_quiet]

theorem kBlocks_quiet (pad : Nat) (cs : List KC) (B : Nat) (tailRun : Bool) (out : Option Nat)
    (n : Nat) : ∀ m k st b, quiet (kBlocks pad cs B tailRun out n m k st b).1 = true
  | 0, _, _, _ => rfl
  | m + 1, k, st, b => by
      simp only [kBlocks, quiet_append, kIns_quiet, kBlocks_quiet pad cs B tailRun out n m]
      rfl

theorem kXorByte_quiet (cs : List KC) (pos v b : Nat) : quiet (kXorByte cs pos v b).1 = true := by
  simp only [kXorByte]
  split <;> rfl

/-- **The Keccak message pops nothing.** -/
theorem kMsg_quiet (pad : Nat) (cells : List KC) (len : Nat) (tailRun : Bool) (out : Option Nat)
    (b n : Nat) : quiet (kMsg pad cells len tailRun out b n).1 = true := by
  simp only [kMsg, quiet_append, kXorByte_quiet, kBlocks_quiet, Bool.and_self]

/-! ## A codeword arm -/

/-- A scheme's chain step pops nothing. -/
def StepQuiet (W : WotsT) : Prop := ∀ i s v c o, quiet (W.step i s v c o) = true

/-- The entry of a chain's start. -/
abbrev startPop (x : E) : Pop := ("chain_starts", [x])

theorem walkT_pops {W : WotsT} (hW : StepQuiet W) (σ : Val) (i : Nat) (slot : Nat → Nat) (stride d b : Nat) :
    FallPops rd σ (walkT W i slot stride d b) [startPop (σ (walkStartV slot d b))] := by
  unfold walkT walkStartV
  split
  · simpa [hintW, Atom.pops, Hint.pops, Dest.words] using FallPops.atom (rd := rd) (σ := σ)
      (.hint (.witness "chain_starts" (.stack [.n (slot 2)])))
  · simpa [hintW, Atom.pops, Hint.pops, Dest.words] using
      (fallPops_quiet (rd := rd) σ (quiet_flatMap _ (fun j => hW _ _ _ _ _) _)).cons_atom
        (a := .hint (.witness "chain_starts" (.stack [.n b])))

theorem walksT_pops {W : WotsT} (hW : StepQuiet W) (σ : Val) (slots : Nat → Nat → Nat) (first k stride : Nat) :
    ∀ m r b, FallPops rd σ (walksT W slots first k stride m r b).1 ((List.range m).map fun j =>
      startPop (σ (walkStartV (slots (r + j)) (k / 4 ^ (r + j) % 4) (walkBase stride k r j b))))
  | 0, _, _ => FallPops.nil
  | m + 1, r, b => by
      simp only [walksT]
      rw [List.range_succ_eq_map, List.map_cons, List.map_map, ← List.singleton_append]
      refine (walkT_pops hW σ _ _ stride _ b).append ?_
      convert walksT_pops hW σ slots first k stride m (r + 1) (b + walkSize stride (k / 4 ^ r % 4)) using 2
      funext j
      simp only [Function.comp_apply, walkBase, show r + (j + 1) = r + 1 + j by omega]

/-- **An arm pops its chains' starts**, in chain order. -/
theorem armT_pops {W : WotsT} (hW : StepQuiet W) (σ : Val) (slots : Nat → Nat → Nat) (first n : Nat)
    (fold : Bool) (prodIn encIn prodOut encOut : V) (k b : Nat) :
    FallPops rd σ (armT W slots first n fold prodIn encIn prodOut encOut k b).1
      ((List.range n).map fun t => startPop (σ (armStart W slots fold k b t))) := by
  have hw := walksT_pops (rd := rd) hW σ slots first k (if k = 0 then W.size + 1 else W.size) n 0
    (if fold then b + 1 else b)
  simp only [Nat.zero_add] at hw
  rw [← List.nil_append ((List.range n).map _), ← List.append_nil ([] ++ _)]
  unfold armT armStart
  cases fold <;> by_cases hk : k = 0 <;> simp only [hk, ↓reduceIte, Bool.false_eq_true] at hw ⊢ <;>
    exact ((fallPops_quiet σ rfl).append hw).append (fallPops_quiet σ rfl)

end
end LeanVM.Guest.B1.Sig
