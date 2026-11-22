"""`child_claim_list_any`'s rules: the callees reading its entries table are linked to it (`anylink.py`,
`Res.anyLink`)."""

ANY_ORIGIN = {'child_claim_list_any'}
# its entries parameter and its bound parameter, `limit = w·g` (`Res.Link`'s `uE`, `uL`)
ANY_PARAMS = {'child_claim_list_any': ('entries_ptr', 'limit_g')}


# ---- its counts (`scripts/count`)

# counted by its tree's shape in the `V` family (`child_claim_list_digest`'s); its frame weight in `VsCountData`
COUNT_SHAPE = {'child_claim_list_any': 'V'}
COUNT_OM = {'child_claim_list_any': ('VsCountData', 3)}

# its own Lean files beside its B1 proofs' `B1/` modules and its `CoreMode/Fn/<f>/` (`fnreg.own_files`): what a change to
# it alone may change, by hand
OWN = [
    'LeanVM/Guest/CoreMode/Fam/ResA.lean',
    'LeanVM/Guest/CoreMode/Fam/LinkDefs.lean',
    'LeanVM/Guest/EndExecCoreLink.lean',
]
