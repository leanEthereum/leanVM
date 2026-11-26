/-
  Rv64mc.Link.Basic

  What a relocatable template knows of the program around it. `scripts/gen.py` writes one template per function
  (`Rv64mc/Gen/Tmpl/`): its lift, `tmpl L`, with every value that depends on where code and data sit a field of a
  structure `Link`. The fields are of three kinds: each callee by its index and entry (`Callee`), each call site by
  the value its `auipc` writes and its `jalr` offset (`Site`), and each PC-relative data reference by its `auipc`
  value, its `lo12` offset and the address they make (`DataRef`). The link step (`Rv64mc/Gen/Link/`) proves of the
  concrete program the predicates below, which a template's `Link.WF` states field by field.

  ## Main results

  * `Callee.WF.addrAt`: a callee's fact in the form of `Isa.addrAt`
  * `callee_site`: a call through a site reaches its callee
  * `DataRef.WF.eval`: a data reference's `lo12` user computes its address
-/

import LprogRiscV.Lsym

namespace Rv64mc

open RiscvZkvm.Rv64 Lprog Lprog.RiscV

/-- A function of the program: its index and its entry. -/
structure Callee where
  idx : Nat
  entry : Word

/-- A call site: the value its `auipc` writes and its `jalr`'s offset, sign-extended. -/
structure Site where
  hi : Word
  lo : Word

/-- A PC-relative data reference: the value its `auipc` writes, the `lo12` offset its users add, sign-extended,
    and the address the two make. -/
structure DataRef where
  hi : Word
  lo : Word
  addr : Word

/-- The callee's index names a function at its entry. Stated with `Isa.addrAt` unfolded, the form a callee's lookup
    takes in `lsym`'s simp set once `Lprog.Isa.addrAt` is in it. -/
def Callee.WF (p : Lprog (Op Reg) Reg) (c : Callee) : Prop := (p[c.idx]?).map (·.addr) = some c.entry

/-- The site reaches the callee's entry. -/
def Site.WF (s : Site) (c : Callee) : Prop := (s.hi + s.lo) &&& 0xfffffffffffffffe#64 = c.entry

/-- The reference's two parts make its address. -/
def DataRef.WF (d : DataRef) : Prop := d.hi + d.lo = d.addr

theorem Callee.WF.addrAt {p : Lprog (Op Reg) Reg} {c : Callee} (h : c.WF p) : rvIsa.addrAt p c.idx = some c.entry :=
  h

/-- **A call through a site reaches its callee**: the `jalr` through register `r` after the site's `auipc`, whose
    only candidate is the callee's index. -/
theorem callee_site {p : Lprog (Op Reg) Reg} {c : Callee} {s : Site} (hc : c.WF p) (hs : s.WF c)
    {regs : Reg → Word} {r : Reg} (h : regs r = s.hi) :
    rvIsa.callee p regs
      (.indirect (.bin .and (.bin .add (.reg r) (.imm s.lo)) (.imm 0xfffffffffffffffe#64)) [c.idx]) =
      some c.idx := by
  simp only [Callee.WF, Site.WF] at hc hs
  simp [Isa.callee, List.find?, Isa.addrAt, hc, Expr.eval, BinOp.eval, h, hs]

/-- A `lo12` user of a data reference, reading the register its `auipc` wrote, computes the reference's address. -/
theorem DataRef.WF.eval {d : DataRef} (hd : d.WF) {regs : Reg → Word} {r : Reg} (h : regs r = d.hi) :
    (Expr.bin .add (.reg r) (.imm d.lo)).eval regs = d.addr := by
  simp only [DataRef.WF] at hd
  simp [Expr.eval, BinOp.eval, h, hd]

end Rv64mc
