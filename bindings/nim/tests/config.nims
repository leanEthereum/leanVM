# Strict compiler checks for the tests. The nimble test task picks the memory manager.
--threads:on
--styleCheck:usages
--styleCheck:error

for warning in [
    "BareExcept", "CaseTransition", "CStringConv", "CycleCreated", "ImplicitDefaultValue",
    "ImplicitTemplateRedefinition", "InvalidCmpOp", "LongLiterals", "StmtListLambda",
    "UnreachableCode", "UnreachableElse", "UnusedImport"]:
  switch("warningAsError", warning & ":on")
for hint in ["ConvFromXtoItselfNotNeeded", "DuplicateModuleImport"]:
  switch("hintAsError", hint & ":on")
switch("hint", "XCannotRaiseY:off")
