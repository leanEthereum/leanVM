/-
  LeanVM.Guest.Memory.StaticVec

  The static weight checker on vectors of weights: one walk of a body checks a certificate per
  coordinate (`chkFnV`), not counting words.
-/

module

public import LeanVM.Guest.Memory.Static

/-!
# The checker on vectors

Several weights of one program (an instruction count per opcode) have certificates of one shape:
the same preconditions, terms and constants, the numbers apart. A **vector certificate**
(`CertV`) holds them all, a number of each replaced by the vector of its coordinates (`Vec`, read
as zero past its end), and `chkFnV` checks it in one walk of the body, `chkFn`'s with the
arithmetic done coordinate by coordinate. Coordinate `i` of a vector certificate is a certificate
(`CertV.proj`), and `StaticVecSound.chkFnV_proj` turns a vector check into the check of each.
-/

namespace LeanVM.Guest.Memory

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core

@[expose] public section

/-! ## Vectors -/

/-- Weights by coordinate, zero past the end. -/
abbrev Vec := List ℕ

def Vec.add : Vec → Vec → Vec
  | [], b => b
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a + b) :: Vec.add as bs

def Vec.max : Vec → Vec → Vec
  | [], b => b
  | a :: as, [] => a :: as
  | a :: as, b :: bs => Max.max a b :: Vec.max as bs

def Vec.scale (n : ℕ) (a : Vec) : Vec := a.map (n * ·)

/-- Coordinate by coordinate at most. -/
def Vec.le : Vec → Vec → Bool
  | [], _ => true
  | a :: as, [] => Nat.beq a 0 && Vec.le as []
  | a :: as, b :: bs => Nat.ble a b && Vec.le as bs

/-- An affine bound by coordinate. -/
structure AffV where
  c : Vec
  cs : List (ℕ × Vec)
  deriving DecidableEq, Repr, Inhabited

/-- Coordinate `i`. -/
def AffV.proj (i : ℕ) (a : AffV) : Aff := ⟨a.c.getD i 0, a.cs.map fun q => (q.1, q.2.getD i 0)⟩

def AffV.add (a b : AffV) : AffV := ⟨a.c.add b.c, a.cs ++ b.cs⟩

def AffV.scale (n : ℕ) (a : AffV) : AffV := ⟨a.c.scale n, a.cs.map fun q => (q.1, q.2.scale n)⟩

def AffV.leB (a b : AffV) : Bool := a.c.le b.c && a.cs == b.cs

/-- A vector certificate: `Cert` with its bound by coordinate. -/
inductive CertV where
  | none
  | stat (pre : List (ℕ × ℕ)) (b : AffV) (ks : List (V × ℕ))
  | loop (endc : Option ℕ) (pre : List (ℕ × ℕ)) (b : AffV) (ks : List (V × ℕ))
  deriving Inhabited

/-- Coordinate `i`. -/
def CertV.proj (i : ℕ) : CertV → Cert
  | .none => .none
  | .stat pre b ks => .stat pre (b.proj i) ks
  | .loop endc pre b ks => .loop endc pre (b.proj i) ks

/-! ## The checker -/

abbrev AccV := AffV × List (ℕ × ℕ)

def AccV.proj (i : ℕ) (r : AccV) : Acc := (r.1.proj i, r.2)

def AccV.zero : AccV := (⟨[], []⟩, [])

def AccV.add (a b : AccV) : AccV := (a.1.add b.1, a.2 ++ b.2)

def AccV.join (a b : AccV) : AccV := (⟨a.1.c.max b.1.c, a.1.cs ++ b.1.cs⟩, a.2 ++ b.2)

def Option.addAccV : Option AccV → Option AccV → Option AccV
  | some a, some b => some (a.add b)
  | _, _ => none

def Option.maxAccV : Option AccV → Option AccV → Option AccV
  | some a, some b => some (a.join b)
  | _, _ => none

def maxBV {α : Type} (f : α → Option AccV) : List α → Option AccV
  | [] => some AccV.zero
  | a :: as => Option.maxAccV (f a) (maxBV f as)

def sumBV {α : Type} (f : α → Option AccV) : List α → Option AccV
  | [] => some AccV.zero
  | a :: as => Option.addAccV (f a) (sumBV f as)

/-- `termB` by coordinate. -/
def termBV (ρ : Env) (ps : List V) (args : List V) (q : ℕ × Vec) : Option AccV :=
  match args[q.1]? with
  | some v => match cls ρ ps v with
    | .pow e => some (⟨q.2.scale e, []⟩, [])
    | .param k => some (⟨[], [(k, q.2)]⟩, [])
    | .none => none
  | none => none

/-- `preB`, its bound zero. -/
def preBV (ρ : Env) (ps : List V) (args : List V) (q : ℕ × ℕ) : Option AccV :=
  match args[q.1]? with
  | some v => match cls ρ ps v with
    | .pow e => if q.2 < e ∧ e < 2 ^ 64 - 1 then some AccV.zero else none
    | .param k => some (⟨[], []⟩, [(k, q.2)])
    | .none => none
  | none => none

def transBV (ρ : Env) (ps : List V) (args : List V) (pre : List (ℕ × ℕ)) (b : AffV) : Option AccV :=
  Option.addAccV (some (⟨b.c, []⟩, []))
    (Option.addAccV (sumBV (termBV ρ ps args) b.cs) (sumBV (preBV ρ ps args) pre))

/-- `siteB` by coordinate, not counting words. -/
def siteBV (cert : String → CertV) (ρ : Env) (ps : List V) (g : String) (args : List V) :
    Option AccV :=
  match cert g with
  | .none => none
  | .stat pre b _ => transBV ρ ps args pre b
  | .loop endc pre b _ =>
      match args[0]? with
      | none => none
      | some v0 => match cls ρ ps v0 with
        | .pow a0 =>
            let endv : VCls := match endc with
              | some e => .pow e
              | none => match args[1]? with
                | some v1 => cls ρ ps v1
                | none => .none
            match endv with
            | .pow e =>
                if a0 < e ∧ e < 2 ^ 64 - 1 then
                  (transBV ρ ps args pre b).map fun r => ((r.1.scale (e - a0)).add ⟨[], []⟩, r.2)
                else none
            | .param k =>
                match transBV ρ ps args pre b with
                | some r => if r.1.cs = [] then some ((⟨[], [(k, r.1.c)]⟩ : AffV).add ⟨[], []⟩, (k, a0) :: r.2)
                  else none
                | none => none
            | .none => none
        | _ => none

/-- The constants after an atom, not counting words (`atomB false`). -/
def envAtom (ks : List (V × ℕ)) (ρ : Env × BEnv) : Atom → Env × BEnv
  | .const v w => match vlookup v ks with
      | some e => if constOk w e then ((v, e) :: ρ.1, ρ.2) else ρ
      | none => ρ
  | _ => ρ

/-- **`stmtR` by coordinate**, not counting words. -/
noncomputable def stmtRV (cert : String → CertV) (ks : List (V × ℕ)) (ps : List V) (self : String) :
    Stmt → Env × BEnv → Option (AccV × Option (Env × BEnv)) :=
  @Stmt.rec (fun _ => Env × BEnv → Option (AccV × Option (Env × BEnv))) (fun _ => Env × BEnv → Option AccV)
    (fun _ => Env × BEnv → Option AccV)
    (fun a ρ => some (AccV.zero, some (envAtom ks ρ a)))
    (fun _ _ _ hz hn ρ => (Option.maxAccV (hz ρ) (hn ρ)).map fun r => (r, some ρ))
    (fun _ _ ha ρ => (ha ρ).map fun r => (r, some ρ))
    (fun g args _ ρ => (siteBV cert ρ.1 ps g args).map fun r => (r, some ρ))
    (fun _ g args ρ => if g = self then none
      else (Option.addAccV (siteBV cert ρ.1 ps g args) (some AccV.zero)).map fun r => (r, some ρ))
    (fun _ gs args _ ρ => (maxBV (fun g => siteBV cert ρ.1 ps g args) gs).map fun r => (r, some ρ))
    (fun _ _ => some (AccV.zero, none))
    (fun _ => some AccV.zero)
    (fun _ _ hs hss ρ => match hs ρ with
      | none => none
      | some (r, some ρ') => Option.addAccV (some r) (hss ρ')
      | some (r, none) => some r)
    (fun _ => some AccV.zero)
    (fun _ _ ha has ρ => Option.maxAccV (ha ρ) (has ρ))

/-- `stmtRV` of a block. -/
noncomputable def blockRV (cert : String → CertV) (ks : List (V × ℕ)) (ps : List V) (self : String) :
    List Stmt → Env × BEnv → Option AccV :=
  @Stmt.rec_1 (fun _ => Env × BEnv → Option (AccV × Option (Env × BEnv))) (fun _ => Env × BEnv → Option AccV)
    (fun _ => Env × BEnv → Option AccV)
    (fun a ρ => some (AccV.zero, some (envAtom ks ρ a)))
    (fun _ _ _ hz hn ρ => (Option.maxAccV (hz ρ) (hn ρ)).map fun r => (r, some ρ))
    (fun _ _ ha ρ => (ha ρ).map fun r => (r, some ρ))
    (fun g args _ ρ => (siteBV cert ρ.1 ps g args).map fun r => (r, some ρ))
    (fun _ g args ρ => if g = self then none
      else (Option.addAccV (siteBV cert ρ.1 ps g args) (some AccV.zero)).map fun r => (r, some ρ))
    (fun _ gs args _ ρ => (maxBV (fun g => siteBV cert ρ.1 ps g args) gs).map fun r => (r, some ρ))
    (fun _ _ => some (AccV.zero, none))
    (fun _ => some AccV.zero)
    (fun _ _ hs hss ρ => match hs ρ with
      | none => none
      | some (r, some ρ') => Option.addAccV (some r) (hss ρ')
      | some (r, none) => some r)
    (fun _ => some AccV.zero)
    (fun _ _ ha has ρ => Option.maxAccV (ha ρ) (has ρ))

/-- `stmtRV` of arms. -/
noncomputable def armsRV (cert : String → CertV) (ks : List (V × ℕ)) (ps : List V) (self : String) :
    List (List Stmt) → Env × BEnv → Option AccV :=
  @Stmt.rec_2 (fun _ => Env × BEnv → Option (AccV × Option (Env × BEnv))) (fun _ => Env × BEnv → Option AccV)
    (fun _ => Env × BEnv → Option AccV)
    (fun a ρ => some (AccV.zero, some (envAtom ks ρ a)))
    (fun _ _ _ hz hn ρ => (Option.maxAccV (hz ρ) (hn ρ)).map fun r => (r, some ρ))
    (fun _ _ ha ρ => (ha ρ).map fun r => (r, some ρ))
    (fun g args _ ρ => (siteBV cert ρ.1 ps g args).map fun r => (r, some ρ))
    (fun _ g args ρ => if g = self then none
      else (Option.addAccV (siteBV cert ρ.1 ps g args) (some AccV.zero)).map fun r => (r, some ρ))
    (fun _ gs args _ ρ => (maxBV (fun g => siteBV cert ρ.1 ps g args) gs).map fun r => (r, some ρ))
    (fun _ _ => some (AccV.zero, none))
    (fun _ => some AccV.zero)
    (fun _ _ hs hss ρ => match hs ρ with
      | none => none
      | some (r, some ρ') => Option.addAccV (some r) (hss ρ')
      | some (r, none) => some r)
    (fun _ => some AccV.zero)
    (fun _ _ ha has ρ => Option.maxAccV (ha ρ) (has ρ))

/-- **The check of a function by coordinate** against its vector certificate `own`, its frame
weighing `w`, its callees' certificates by `look`. -/
noncomputable def chkFnV (look : String → CertV) (own : CertV) (w : Vec) (fn : Fn) : Bool :=
  match own with
  | .none => true
  | .stat pre b ks =>
      match blockRV look ks fn.params fn.name fn.body ([], []) with
      | some r => AffV.leB ⟨w.add r.1.c, r.1.cs⟩ b && r.2.all (· ∈ pre)
      | none => false
  | .loop endc pre b ks =>
      match loopShape fn endc with
      | some pre' => match blockRV look ks fn.params fn.name pre' ([], []) with
        | some r => AffV.leB ⟨w.add r.1.c, r.1.cs⟩ b && r.2.all (· ∈ pre) &&
            b.cs.all (·.1 ≠ 0) && pre.all (·.1 ≠ 0)
        | none => false
      | none => false

end
end LeanVM.Guest.Memory
