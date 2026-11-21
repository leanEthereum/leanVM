"""`child_claim_list_any`'s rules: the callees reading its entries table are linked to it (`anylink.py`,
`Res.anyLink`)."""

ANY_ORIGIN = {'child_claim_list_any'}

# its own Lean files (beside its B1 proofs' `B1/` modules): what a change to it alone may change, by hand
OWN = [
    'LeanVM/Guest/CoreMode/Fam/ResA.lean',
    'LeanVM/Guest/CoreMode/Fam/LinkDefs.lean',
    'LeanVM/Guest/EndExecCoreLink.lean',
]
