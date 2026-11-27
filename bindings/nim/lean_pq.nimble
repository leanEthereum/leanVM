mode = ScriptMode.Verbose

packageName   = "lean_pq"
version       = "0.19.1" # x-release-please-version
author        = "The leanVM contributors"
description   = "leanXMSS and leanSPHINCS post-quantum signatures and their recursive aggregation"
license       = "MIT or Apache License 2.0"
# Nimble's default file selection would leave the header out. The first build downloads the
# native archive into `native/` (lean_pq/abi.nim).
installFiles  = @["lean_pq.nim"]
installDirs   = @["lean_pq", "include"]

requires "nim >= 2.2.12"
requires "results"

taskRequires "test", "unittest2"

task test, "Run the tests under refc and orc":
  for mm in ["refc", "orc"]:
    exec "nim c -r -d:release --mm:" & mm & " --nimcache:nimcache/" & mm &
      " --outdir:nimcache tests/test_lean_pq.nim"
