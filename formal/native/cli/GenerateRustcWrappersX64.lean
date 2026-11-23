module

public meta import RustcIngest.X64
public meta import RustcIngest.Generate

public meta def main (args : List String) : IO UInt32 :=
  Ingest.writeWrappers x64 "x86_64" "X64" "ingest_x64" args
