/-
  LeanVM.Guest.CoreMode.SigIx

  The callees' signatures of a heap check read by number: each name's key (`strKey`, its bytes as a
  number) compared instead of the name, equal to the lookup by name, faster in the kernel.
-/

module

public import LeanVM.Guest.CoreMode.Defs

/-!
# The callees' signatures, by key

A heap check reads a callee's signature at each call and several times for each arm of a dispatch, through
`fun f ↦ bif f == core.name then hcert.sig else (csigs.lookup f).getD {}` (`heapwin.py`'s `sigW`): a scan of the
callee list comparing strings, which the kernel does byte by byte through their UTF-8 encodings. `strKey` reads a
string's bytes as one number, injectively (`strKey_inj`), so `sigK` does the same lookup comparing numbers, the callee
list's keys stated once (`sigK_eq`). `heapwin.py` uses it for a function with many callees (`SIGK`), where the scan
dominates the check.
-/

namespace LeanVM.Guest.CoreMode

@[expose] public section

/-- A byte list as a number: its bytes the base-256 digits, the first the least significant, under a top
digit `1`. -/
def bytesKey (l : List UInt8) : ℕ := l.foldr (fun b h ↦ h * 256 + b.toNat) 1

/-- **A string's key**: its UTF-8 bytes as one number (`bytesKey`). -/
def strKey (s : String) : ℕ := bytesKey s.toByteArray.data.toList

private theorem bytesKey_cons (b : UInt8) (l : List UInt8) : bytesKey (b :: l) = bytesKey l * 256 + b.toNat :=
  rfl

private theorem one_le_bytesKey : ∀ l : List UInt8, 1 ≤ bytesKey l
  | [] => Nat.le_refl 1
  | b :: l => by have := one_le_bytesKey l; rw [bytesKey_cons]; omega

private theorem bytesKey_inj : ∀ {l l' : List UInt8}, bytesKey l = bytesKey l' → l = l'
  | [], [], _ => rfl
  | [], b :: l, h | b :: l, [], h => by
    have := one_le_bytesKey l
    have : bytesKey [] = 1 := rfl
    rw [bytesKey_cons] at h
    omega
  | b :: l, b' :: l', h => by
    have := b.toNat_lt; have := b'.toNat_lt
    rw [bytesKey_cons, bytesKey_cons] at h
    obtain rfl : b = b' := UInt8.toNat_inj.mp (by omega)
    rw [bytesKey_inj (by omega : bytesKey l = bytesKey l')]

theorem strKey_inj {s t : String} (h : strKey s = strKey t) : s = t :=
  String.toByteArray_inj.mp (ByteArray.ext (Array.toList_inj.mp (bytesKey_inj h)))

private theorem beq_strKey (s t : String) : Nat.beq (strKey s) (strKey t) = (s == t) :=
  Bool.eq_iff_iff.mpr (by rw [Nat.beq_eq, beq_iff_eq]; exact ⟨strKey_inj, congrArg strKey⟩)

/-- The value of the first entry of `L` whose key (the entry of `K` at its position) is `k`. -/
def lookupK {β : Type} (k : ℕ) : List ℕ → List (String × β) → Option β
  | k' :: K, p :: L => bif Nat.beq k k' then some p.2 else lookupK k K L
  | _, _ => none

private theorem lookupK_eq {β : Type} (g : String) :
    ∀ L : List (String × β), lookupK (strKey g) (L.map fun p ↦ strKey p.1) L = L.lookup g
  | [] => rfl
  | (n, G) :: L => by
    rw [List.map_cons, lookupK, beq_strKey, lookupK_eq g L, List.lookup_cons]
    cases g == n <;> rfl

/-- **The callees' signatures by key**: the own signature `sig` at the key `own`, else the first entry of `L`
at the name's key (`K` the keys of `L`'s names), else none. -/
def sigK (own : ℕ) (sig : HSig) (K : List ℕ) (L : List (String × HSig)) (g : String) : HSig :=
  bif Nat.beq (strKey g) own then sig else (lookupK (strKey g) K L).getD {}

/-- **The lookup by name is the lookup by key**, `own` the own name's key and `K` the callees'. -/
theorem sigK_eq {name : String} {sig : HSig} {L : List (String × HSig)} {own : ℕ} {K : List ℕ}
    (hown : strKey name = own) (hK : L.map (fun p ↦ strKey p.1) = K) :
    (fun f ↦ bif f == name then sig else (L.lookup f).getD {}) = sigK own sig K L := by
  subst hown hK
  funext g
  rw [sigK, lookupK_eq, beq_strKey]

end

end LeanVM.Guest.CoreMode
