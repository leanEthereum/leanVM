"""`child_claim_list_any`'s rules: the callees reading its entries table are linked to it (`anylink.py`,
`Res.anyLink`)."""

ANY_ORIGIN = {'child_claim_list_any'}
# its entries parameter and its bound parameter, `limit = w·g` (`Res.Link`'s `uE`, `uL`)
ANY_PARAMS = {'child_claim_list_any': ('entries_ptr', 'limit_g')}


# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = [
    'LeanVM/Guest/CoreMode/Fam/LinkDefs.lean',
]
