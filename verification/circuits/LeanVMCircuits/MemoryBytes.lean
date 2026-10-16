module

public import LeanVMCircuits.MemorySemantics

@[expose] public section

namespace LeanVMCircuits.Memory

variable {F G : Type}

def byte (j : Fin 8) (word : Vector F 64) : Vector F 8 :=
  Vector.mapFinRange 8 fun i => word[8 * j.val + i.val]'(by omega)

def joinBytes (bytes : Vector (Vector F 8) 8) : Vector F 64 :=
  Vector.mapFinRange 64 fun i => (bytes[i.val / 8]'(by omega))[i.val % 8]'(by omega)

theorem byte_map (f : F → G) (j : Fin 8) (word : Vector F 64) :
    (byte j word).map f = byte j (word.map f) := by
  apply Vector.ext
  intro i hi
  simp only [byte, Vector.getElem_map, Vector.getElem_mapFinRange]

theorem joinBytes_map (f : F → G) (bytes : Vector (Vector F 8) 8) :
    (joinBytes bytes).map f = joinBytes (bytes.map (fun word => word.map f)) := by
  apply Vector.ext
  intro i hi
  simp only [joinBytes, Vector.getElem_map, Vector.getElem_mapFinRange]

theorem joinBytes_byte (word : Vector F 64) :
    joinBytes (Vector.ofFn fun j => byte j word) = word := by
  apply Vector.ext
  intro i hi
  simp only [joinBytes, byte, Vector.getElem_mapFinRange, Vector.getElem_ofFn]
  congr 1
  omega

end LeanVMCircuits.Memory
