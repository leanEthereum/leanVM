mode = ScriptMode.Verbose

packageName   = "lean_pq"
version       = "0.11.0" # x-release-please-version
author        = "The lean-pq-bindings contributors"
description   = "leanXMSS and leanSPHINCS post-quantum signatures and their recursive aggregation"
license       = "MIT or Apache License 2.0"
# `native` holds the bundled static archives in release packages; Nimble's default file selection
# would leave them and the header out.
installFiles  = @["lean_pq.nim"]
installDirs   = @["lean_pq", "include", "native"]

requires "nim >= 2.2.12"
requires "results"

taskRequires "test", "unittest2"

task test, "Run the tests under refc and orc":
  for mm in ["refc", "orc"]:
    exec "nim c -r -d:release --mm:" & mm & " --nimcache:nimcache/" & mm &
      " --outdir:nimcache tests/test_lean_pq.nim"
