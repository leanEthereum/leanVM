"""Contracts given by hand (`sigc.py`), for functions that have no signature as written (new to the guest, their frame
layout changed, or named by `sigc.py --fresh`): by stable name, the literal fields of `Fn.«k».csig : Mode.Sig` past its entry, as
`CoreMode/Sig/<pack>.lean` writes them (entry cells, self cell, pre, preR, term, return cells, post, postR, postL, preP,
postP, postLP, retV, postT, postC). The route's checks hold each to the function's heap signature (`CoreMode.ownOk`,
`fitB`) like any other."""
SEEDS = {}
