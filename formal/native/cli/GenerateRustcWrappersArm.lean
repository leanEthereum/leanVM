module

public meta import RustcIngest.Arm
public meta import RustcIngest.Generate

public meta def main (args : List String) : IO UInt32 :=
  Ingest.writeWrappers arm "aarch64" "Arm" "ingest_arm" args
